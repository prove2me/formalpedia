-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_linearEquiv_cech_pushforward_of_finite
-- name    : AlgebraicGeometry.SmoothProperCurve.exists_linearEquiv_cech_pushforward_of_finite
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-13T17:08:23.8223+00:00
-- url     : https://prove2.me/theorems/7c0772d8-f8ac-4994-b9cd-e04385ccbb3f
-- title:
--   Two-chart cohomology comparison for finite pushforward on smooth proper curves
-- statement:
--   Let $K$ be a field, let $C$ and $D$ be smooth proper integral curves over $K$, and let $g:D\to C$ be a finite $K$-morphism. Choose covers $\mathcal U$ of $C$ and $\mathcal V$ of $D$ by two affine opens. For every invertible sheaf $M$ on $D$, there are $K$-linear isomorphisms
--
--   $$\check H^i(\mathcal V,M)\simeq\check H^i(\mathcal U,g_*M),\qquad i=0,1.$$
--
--   The covers may be chosen independently. The statement compares the actual cohomology spaces and in particular identifies their Euler characteristics.
--
--   **Formalization Note.** The formal conclusion uses the existing kernel and cokernel section modules of the two-chart Cech complex. The equality of the structure morphisms specifies that $g$ is a morphism over $K$.
-- source:
--   Specialization of Stacks Project, Tag 089W (https://stacks.math.columbia.edu/tag/089W), to finite morphisms and invertible sheaves, combined with the affine-cover comparison in Section 30.2, Lemma 30.2.6 (https://stacks.math.columbia.edu/tag/01X8). Finite morphisms are affine and invertible sheaves are quasi-coherent. Proper curves are separated, so the specified affine covers compute cohomology; the comparisons are K-linear for a K-morphism. The formal statement specializes the cohomological comparison to degrees zero and one.

import Definitions.Def_AlgebraicGeometry_CurveDegreeTests
import Mathlib.AlgebraicGeometry.Morphisms.Finite

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u

theorem AlgebraicGeometry.SmoothProperCurve.exists_linearEquiv_cech_pushforward_of_finite
    (K : Type u) [Field K] {C D : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) (δ : D ⟶ Spec (.of K))
    [IsIntegral C] [IsIntegral D] [IsProper c] [IsProper δ]
    [SmoothOfRelativeDimension 1 c] [SmoothOfRelativeDimension 1 δ]
    (g : D ⟶ C) [IsFinite g] (hg : g ≫ c = δ)
    (𝒰 : C.TwoAffineOpenCover) (𝒱 : D.TwoAffineOpenCover)
    (M : D.Modules) (hM : Scheme.Modules.IsInvertible M) :
    Nonempty ((𝒱.sectionsOf δ M).H0 ≃ₗ[K]
      (𝒰.sectionsOf c ((Scheme.Modules.pushforward g).obj M)).H0) ∧
    Nonempty ((𝒱.sectionsOf δ M).H1 ≃ₗ[K]
      (𝒰.sectionsOf c ((Scheme.Modules.pushforward g).obj M)).H1) := by
  sorry
