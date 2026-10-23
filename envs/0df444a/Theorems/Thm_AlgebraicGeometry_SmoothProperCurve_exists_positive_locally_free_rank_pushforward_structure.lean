-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_positive_locally_free_rank_pushforward_structure
-- name    : AlgebraicGeometry.SmoothProperCurve.exists_positive_locally_free_rank_pushforward_structure
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-13T17:08:24.04664+00:00
-- url     : https://prove2.me/theorems/281b81b3-d39d-4f90-baae-d84f05b5b7b7
-- title:
--   Positive locally free rank of the structure-sheaf pushforward along a finite curve cover
-- statement:
--   Let $K$ be a field, let $C$ and $D$ be smooth proper integral curves over $K$, and let $g:D\to C$ be a finite surjective $K$-morphism. The sheaf $g_*\mathcal O_D$ is locally free of a single positive finite rank: there is an integer $d>0$ such that every point of $C$ has an open neighbourhood $U$ with
--
--   $$(g_*\mathcal O_D)|_U\simeq\mathcal O_U^{\oplus d}.$$
--
--   The rank is independent of the point. No separability or algebraic-closedness hypothesis is imposed. This gives the positive rank used in the Euler-characteristic formula for finite curve maps.
--
--   **Formalization Note.** Local freeness of rank $d$ is expressed by actual sheaf isomorphisms on open neighbourhoods, using the existing free sheaf on $d$ generators.
-- source:
--   Consequence of the Stacks Project: flatness of nonconstant maps to normal curves, Tag 0CCK (https://stacks.math.columbia.edu/tag/0CCK); finite flat maps over a locally Noetherian base are finite locally free, Tag 02KB (https://stacks.math.columbia.edu/tag/02KB); and the open-and-closed rank decomposition, Tag 04MH (https://stacks.math.columbia.edu/tag/04MH). Smooth C is normal and Noetherian. Its integrality makes the rank constant; surjectivity makes it positive. This is the resulting constant-rank statement for actual sheaf pushforward.

import Definitions.Def_AlgebraicGeometry_CurveDegreeTests
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u

theorem AlgebraicGeometry.SmoothProperCurve.exists_positive_locally_free_rank_pushforward_structure
    (K : Type u) [Field K] {C D : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) (δ : D ⟶ Spec (.of K))
    [IsIntegral C] [IsIntegral D] [IsProper c] [IsProper δ]
    [SmoothOfRelativeDimension 1 c] [SmoothOfRelativeDimension 1 δ]
    (g : D ⟶ C) [IsFinite g] [Surjective g] (hg : g ≫ c = δ) :
    ∃ d : ℕ, 0 < d ∧ ∀ x : C, ∃ U : C.Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj
        ((Scheme.Modules.pushforward g).obj (𝟙_ D.Modules)) ≅
          SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin d))) := by
  sorry
