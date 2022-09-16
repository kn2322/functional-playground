I'm just starting to learn about type-level programming, and I'd like to share some ideas I'd been exploring, along with some questions.

As you may know, recursive functions can be derived from non-recursive functions by an application of `fix :: (t -> t) -> t`. Here, we look at type-level fixed points given by the wrapper datatype `Fix :: (* -> *) -> *`, which allow us to derive recursive types from non-recursive ones.

\begin{code}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
import Prelude hiding (foldr)
\end{code}

\begin{code}
data Fix f = Fix (f (Fix f))
-- Fix :: f (Fix f) -> Fix f

unFix :: Fix f -> f (Fix f)
unFix (Fix x) = x

fix :: (t -> t) -> t
fix f = f (fix f)
\end{code}

For example,

\begin{code}
data ListK a b = NilK | ConsK a b
type List a = Fix (ListK a)

-- elements of List a are things like
-- Fix NilK. Fix (ConsK x (Fix NilK))
-- Fix (ConsK x (Fix (ConsK y NilK)))

-- Claim: List a is 'isomoprhic' to [a]
toMyList :: [a] -> List a
toMyList [] = Fix NilK
toMyList (x:xs) = Fix (ConsK x (toMyList xs))

-- conversely,
fromMyList :: List a -> [a]
fromMyList (Fix NilK) = []
fromMyList (Fix (ConsK x xs)) = x : fromMyList xs
\end{code}

Now, I am very unsure about what isomorphic should mean (any explanation would be a gift). For now let us note that `toMyList` has a nice expression in terms of a `fold`, and `fromMyList` has a nice expression in terms of an `unfold`.

\begin{code}
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr f e [] = e
foldr f e (x:xs) = f x (foldr f e xs)

unfoldr :: (b -> Maybe (a, b)) -> b -> [a]
unfoldr ask v = case ask v of
    Nothing -> []
    Just (x, v') -> x : unfoldr ask v'
\end{code}

\begin{code}
toMyList' = foldr (\x res -> Fix (ConsK x res)) (Fix NilK)
fromMyList' = unfoldr ask
    where
        ask :: List a -> Maybe (a, List a)
        ask (Fix NilK) = Nothing
        ask (Fix (ConsK x xs)) = Just (x, xs)
\end{code}

To give us some more intuition before diving deeper, can you work out which (familiar) types the following fixed points are 'isomorphic' to?

< Fix []

< >!data BTree = Leaf | Fork BTree BTree!<

< Fix Maybe

< >!data Nat = Z | S Nat!<

< Fix ((->) a)

< >!()!<

The 'isomorphisms' are given by

\begin{code}
data BTree = Leaf | Fork BTree BTree deriving Show
data Nat = Z | S Nat deriving Show
toA :: BTree -> Fix []
toA Leaf = Fix []
toA (Fork l r) = Fix ((toA l) : unFix (toA r))

fromA :: Fix [] -> BTree
fromA (Fix []) = Leaf
fromA (Fix (x : xs)) = Fork (fromA x) (fromA (Fix xs))

toB :: Nat -> Fix Maybe
toB Z = Fix Nothing
toB (S n) = Fix (Just (toB n))

fromB :: Fix Maybe -> Nat
fromB (Fix Nothing) = Z
fromB (Fix (Just x)) = S (fromB x)

toC :: () -> Fix ((->) a)
toC () = Fix (\x -> toC ())

fromC :: Fix ((->) a) -> ()
fromC f = ()
\end{code}

Now, I introduce (two) pieces of magic to make the examples so far more interesting. My guiding question was: How can we define functions from `Fix f`? Can we define a fold? Can we define nice functions from `Fix f` in terms of folds from `f`?

\begin{code}
lift :: Functor f => (f b -> b) -> Fix f -> b
lift f = fix (\u -> f . fmap u . unFix)

refix :: Functor f => (a -> f a) -> a -> Fix f
refix f = fix (\u -> Fix . fmap u . f)
\end{code}

I wrote down `lift` and `refix`, but I am still far from understanding their full power (thanks/no thanks to the type-checker).

First, an application:

\begin{code}
-- where UndecidableInstances come in
instance (Functor f, Show (f String)) => Show (Fix f) where
    show = lift show

nu :: Fix []
nu = Fix (Fix (Fix [] : Fix [] : []) : Fix [] : [])

-- *Main> nu
-- ["[\"[]\",\"[]\"]","[]"]
\end{code}

Just like that, we can now print fix point types to our hearts' content.

`lift` and `refix` are able to 'lift' `fold` and `unfold` of `f` to the corresponding `fold` and `unfold` of `Fix f`. `lift` allows us to naturally define functions from fix point types, while 'refix' allows us to naturally define functions to fix point types. The two combinators are in some (categorical?) sense duals of each other.

Taking `f = [], Fix f = Fix []` as our example, we have the following theorems. Let

\begin{code}
-- foldr, unfoldr copied here for reference
foldr' :: (a -> b -> b) -> b -> [a] -> b
foldr' f e [] = e
foldr' f e (x:xs) = f x (foldr' f e xs)

foldF :: (b -> b -> b) -> b -> Fix [] -> b
foldF f e (Fix []) = e
foldF f e (Fix (x : xs)) = f (foldF f e x) (foldF f e (Fix xs))
-- foldF is what you get if you try to define a fold from Fix []
-- Note how its structure is similar to the fold from BTree

-- Theorem:
-- forall e :: b, f :: b -> b -> b.
-- foldF f e = lift (foldr f e)

unfoldr' :: (b -> Maybe (a, b)) -> b -> [a]
unfoldr' ask v = case ask v of
    Nothing -> []
    Just (x, v') -> x : unfoldr' ask v'

unfoldF :: (t -> Maybe (t, t)) -> t -> Fix []
unfoldF ask v = case ask v of
    Nothing -> Fix []
    Just (x, v') -> Fix (unfoldF ask x : unFix (unfoldF ask v'))
-- (Dually?) unfoldF is what you get if you try to define an unfold to Fix []

-- Theorem:
-- forall ask :: t -> Maybe (t, t).
-- unfoldF ask = refix (unfoldr ask)

-- Proof: By induction, and an exercise! I will reproduce it if asked, o/w this post is getting long as it is
\end{code}

In other words, fold of fix is (basically) fix of fold, and unfold of fix is (basically) fix of unfold. Isn't that amazing? Folds on `[]` now exhaustively describe folds on `BTree`.

I suspect there is a (categorical?) datatype generic way to express these two theorems for any algebraic datatype `f :: * -> *` with an instance of `Functor`, which I do not know.

An immediate application is more elegant functions for type isomorphisms, and a way to 'derive' `fold` and `unfold` for `Fix f` from `fold` and `unfold` for `f`.

\begin{code}
toBTree :: Fix [] -> BTree
toBTree = lift (foldr Fork Leaf)

fromBTree :: BTree -> Fix []
fromBTree = refix (unfoldr ask)
    where
        ask :: BTree -> Maybe (BTree, BTree)
        ask Leaf = Nothing
        ask (Fork l r) = Just (l, r)

-- nu :: Fix []
-- nu = Fix (Fix (Fix [] : Fix [] : []) : Fix [] : [])
-- ["[\"[]\",\"[]\"]","[]"]
nu' = toBTree nu
-- Fork (Fork Leaf (Fork Leaf Leaf)) (Fork Leaf Leaf)
nu'' = fromBTree nu'
-- ["[\"[]\",\"[]\"]","[]"]
-- = nu

foldF' :: (b -> b -> b) -> b -> Fix [] -> b
foldF' f e = lift (foldr f e)

unfoldF' :: (t -> Maybe (t, t)) -> t -> Fix []
unfoldF' ask = refix (unfoldr ask)
\end{code}

Compare this with `toA` and `fromA`, `foldF` and `unfoldF`.

You might be curious about how `lift` and `refix` were derived.
1. Write foldF, notice the structural similarities with foldr
2. Transform foldF algebraically to equivalent functions (perhaps 5-6 times), trying to extract foldr from it. Use the type-checker to reassure yourself as you go
3. Arrive at the equation `foldF f e = fix (\u -> foldF f e . fmap u . unFix)`, and go 'aha!', noticing that we can abstract over `foldF f e` by defining `lift g = fix (\u -> g . fmap u . unFix)`
4. Remove the type you originally had for lift in terms of `Fix []`, and let the type-checker tell you its magical type `lift :: Functor f => (f b -> b) -> Fix f -> b`
5. Apply analogies of steps 1-4 to unfoldF and unfoldr to get refix.
6. Scratch your head about why lift is so general that it makes no mention of folds or lists

I had hoped to 'derive' refix after the derivation of lift as an immediate consequence, but I could not figure it out. I suspect it is possible, given how their derivations follow the same steps, and their definitions are almost the reverse of each other.

Next, let us do some type-level magic following the question: how are types which are fixed by a given 'f :: * -> *' related?

\begin{code}
class FixedByList a where
    flatten :: [a] -> a -- should be inverses, and isomorphisms, whatever that means
    raise :: a -> [a]

    toFix :: a -> Fix [] -- Fix [] is a canonical type of the type class (in some sense)
    toFix = refix raise
    fromFix :: Fix [] -> a
    fromFix = lift flatten
    translate :: FixedByList b => a -> b -- defines a (???) over the typeclass FixedByList
    translate = fromFix . toFix

instance FixedByList (Fix []) where -- where FlexibleInstances come in
    flatten = Fix
    raise = unFix

instance FixedByList a => FixedByList [a] where -- applying [] should not change anything if you are fixed by []
    flatten = fmap flatten
    raise = fmap raise

instance FixedByList BTree where
    flatten = foldr Fork Leaf
    raise = unfoldr ask
        where
            ask Leaf = Nothing
            ask (Fork l r) = Just (l, r)

-- *Main> translate nu :: Fix []
-- ["[\"[]\",\"[]\"]","[]"]
-- *Main> translate nu :: [Fix []]
-- [["[]","[]"],[]]
-- *Main> translate nu :: [[Fix []]]
-- [[[],[]],[]]
-- *Main> translate nu :: [[[Fix []]]]
-- [[[],[]],[]]

-- *Main> translate nu :: BTree
-- Fork (Fork Leaf (Fork Leaf Leaf)) (Fork Leaf Leaf)
-- *Main> translate nu :: [BTree]
-- [Fork Leaf (Fork Leaf Leaf),Leaf]
-- *Main> translate nu :: [[BTree]]
-- [[Leaf,Leaf],[]]
-- *Main> translate nu :: [[[BTree]]]
-- [[[],[]],[]]
-- *Main> translate nu :: [[[[BTree]]]]
-- [[[],[]],[]]
\end{code}

Notably, we can show that a type `a` is isomorphic to `Fix []` by just providing `flatten` and `raise`, without needing to think about the fix point type at all!

The above type class `FixedByList` generalises to a multi-parameter type class `Fixes :: (* -> *) -> * -> Constraint` where `FixedByList = Fixes []` with minimal changes (as lift and refix have very general types).

The one exception is `translate`, where GHC complains with the following error:
```
• Could not deduce (Functor f0)
   from the context: (Functor f, Fixes f a, Fixes f b)
     bound by the type signature for:
                translate :: forall (f :: * -> *) a b.
                             (Functor f, Fixes f a, Fixes f b) =>
                             a -> b
     at btree_and_generalise.hs:36:14-56
   The type variable ‘f0’ is ambiguous
 • In the ambiguity check for ‘translate’
   To defer the ambiguity check to use sites, enable AllowAmbiguousTypes
   In the type signature:
     translate :: (Functor f, Fixes f a, Fixes f b) => a -> b
```
And if I enable AllowAmbiguousTypes:
```
• Could not deduce (Fixes f0 a) arising from a use of ‘toFix’
  from the context: (Functor f, Fixes f a, Fixes f b)
    bound by the type signature for:
               translate :: forall (f :: * -> *) a b.
                            (Functor f, Fixes f a, Fixes f b) =>
                            a -> b
    at btree_and_generalise.hs:36:1-56
  The type variable ‘f0’ is ambiguous
  Relevant bindings include
    translate :: a -> b (bound at btree_and_generalise.hs:37:1)
  These potential instances exist:
    instance (Functor f, Fixes f a) => Fixes f (f a)
      -- Defined at btree_and_generalise.hs:21:10
    instance Fixes f (Fix f)
      -- Defined at btree_and_generalise.hs:25:10
    instance Fixes (Either a) (Chain a)
      -- Defined at btree_and_generalise.hs:61:10
    ...plus five others
    ...plus one instance involving out-of-scope types
    (use -fprint-potential-instances to see them all)
• In the second argument of ‘(.)’, namely ‘toFix’
  In the expression: fromFix . toFix
  In an equation for ‘translate’: translate = fromFix . toFix
```
I do not know why (can provide full code if necessary).

Finally, I wish to leave you with some vague but perhaps fruitful questions.

1. What does it *mean* for a type to be the fix point of another? Take `BTree`, we have deduced that `[BTree]` is essentially the same as `BTree`, so any data can be viewed as members of either type. We can say that 'Having a list of `BTree`s is no different from having a single `BTree`'. In this specific case, we can say that a `[BTree]` is viewing `BTree` via a decomposition along its right descendants. What about more generally?
2. An algebraic approach: Can we describe a given datatype in terms of the fix point equations it satisfies? If we say that type `a` is invariant under `[], Maybe, ...`, what do we now know about `a`'s structure and how we might work with it? A related question is: Are there any methods for showing that a given type does not satisfy a fix point equation? E.g. Is `Nat` fixed by `[]`? (I think the answer is yes if we disallow infinite values, no otherwise (without proof))
3. Is there a rigorous foundation for this style of reasoning?
\begin{code}
data RoseTree a = Node a [RoseTree a]
{-
x :: Fix RoseTree implies x = Fix Node y ys
where y :: Fix RoseTree, ys :: [RoseTree (Fix RoseTree)]

So a = Fix RoseTree satisfies the following isomorphism
a ~ (a, [a])
~ nonempty lists of a
-}
data IList a = Only a | Cons a (IList a) deriving Show -- inhabited list
{-
Only :: Fix IList -> IList (Fix IList)
~ Fix IList -> Fix IList
Cons :: Fix IList -> IList (Fix IList) -> IList (Fix IList)
~ Fix IList -> Fix IList -> Fix IList
Inspecting the types of the constructors, a ~ a kind of infinite binary tree, which I call StreamTree below
-}
data StreamTree = Next StreamTree | Branch StreamTree StreamTree deriving Show

class Fixes f a where -- read 'f fixes a'
-- where MultiParamTypeClasses come in
    flatten' :: f a -> a
    raise' :: a -> f a

instance Fixes RoseTree StreamTree where
    flatten' (Node x []) = Next x
    flatten' (Node x xs) = Branch x (f (fmap flatten' xs))
        where
            f :: [StreamTree] -> StreamTree
            f [z] = Next z
            f (z:zs) = Branch z (f zs)

    raise' (Next x) = Node x []
    raise' (Branch l r) = Node l (fmap raise' (g r))
        where
            g :: StreamTree -> [StreamTree]
            g (Next z) = [z]
            g (Branch z zs) = z : g zs
\end{code}

Where the instance `Fixes RoseTree StreamTree` appears to work, as `flatten` and `raise` are indeed inverses (mod some things I don't understand about induction and infinite values).
