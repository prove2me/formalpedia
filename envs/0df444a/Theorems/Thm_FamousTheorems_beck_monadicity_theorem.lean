-- Prove2me | Theorems.Thm_FamousTheorems_beck_monadicity_theorem
-- name    : FamousTheorems.beck_monadicity_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:23:15.804376+00:00
-- url     : https://prove2.me/theorems/46d024a8-a624-4a11-af87-7bfb95b4808a
-- title:
--   Beck's monadicity theorem
-- statement:
--   **Beck's monadicity theorem.** Let $G:\mathcal D\to\mathcal C$ be a functor with a left adjoint $F$. Suppose that $G$ reflects isomorphisms, that $\mathcal D$ has coequalisers of all $G$-split pairs, and that $G$ preserves them. Then $G$ is monadic: the comparison functor from $\mathcal D$ to the category of algebras over the monad $GF$ is an equivalence.
--
--   Beck's theorem characterises categories of algebras over monads. It shows, for example, that groups, rings and modules are monadic over sets, and that compact Hausdorff spaces are monadic over sets via the ultrafilter monad. It is the basis of descent theory.
--
--   **Formalization note.** Mathlib's `CategoryTheory.Monad.monadicOfHasPreservesGSplitCoequalizersOfReflectsIsomorphisms`, which constructs the monadicity data; the statement asserts that `CategoryTheory.MonadicRightAdjoint G` is inhabited. The two categories share a morphism universe.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `CategoryTheory.Monad.monadicOfHasPreservesGSplitCoequalizersOfReflectsIsomorphisms`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

universe v

theorem beck_monadicity_theorem {C D : Type*} [CategoryTheory.Category.{v} C] [CategoryTheory.Category.{v} D]
    {G : CategoryTheory.Functor D C} {F : CategoryTheory.Functor C D} (adj : CategoryTheory.Adjunction F G)
    [G.ReflectsIsomorphisms] [CategoryTheory.Monad.HasCoequalizerOfIsSplitPair G]
    [CategoryTheory.Monad.PreservesColimitOfIsSplitPair G] : Nonempty (CategoryTheory.MonadicRightAdjoint G) := by sorry

end FamousTheorems
