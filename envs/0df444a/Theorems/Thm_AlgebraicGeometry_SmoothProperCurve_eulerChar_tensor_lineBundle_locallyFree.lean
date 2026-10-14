-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_eulerChar_tensor_lineBundle_locallyFree
-- name    : AlgebraicGeometry.SmoothProperCurve.eulerChar_tensor_lineBundle_locallyFree
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-13T17:08:50.743181+00:00
-- url     : https://prove2.me/theorems/e317c3cc-61cb-44b6-a5be-798c7845c31a
-- title:
--   Euler characteristic of a line bundle tensored with a vector bundle on a curve
-- statement:
--   Let $K$ be a field and let $C$ be a smooth proper integral curve over $K$. Let $E$ be a locally free sheaf of constant finite rank $d$, and let $L$ be an invertible sheaf on $C$. For a cover $\mathcal U$ by two affine opens, write
--
--   $$\chi(M)=\dim_K\check H^0(\mathcal U,M)-\dim_K\check H^1(\mathcal U,M).$$
--
--   Then
--
--   $$\chi(L\otimes E)=d\bigl(\chi(L)-\chi(\mathcal O_C)\bigr)+\chi(E).$$
--
--   The rank $d$ may be zero. The statement applies to arbitrary vector bundles $E$, without choosing a finite curve map, and supplies the Euler identity needed for degree scaling.
--
--   **Formalization Note.** The locally free hypothesis specifies open-neighbourhood isomorphisms from $E$ to the free sheaf on $d$ generators. Euler characteristics are expressed using the existing two-chart section modules.
-- source:
--   Specialization of Stacks Project, Lemma 33.44.5, Tag 0AYV (https://stacks.math.columbia.edu/tag/0AYV): take its locally free sheaf to be L of rank one and its coherent sheaf to be E of rank d. Use the degree definition deg(L) = chi(L) - chi(O_C) from Definition 33.44.1 (https://stacks.math.columbia.edu/tag/0AYQ). Affine Cech cohomology on the separated curve computes the Euler characteristic. This is the explicit two-chart formulation of that specialization.

import Definitions.Def_AlgebraicGeometry_CurveDegreeTests
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u

theorem AlgebraicGeometry.SmoothProperCurve.eulerChar_tensor_lineBundle_locallyFree
    (K : Type u) [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsIntegral C] [IsProper c]
    [SmoothOfRelativeDimension 1 c] (𝒰 : C.TwoAffineOpenCover)
    (d : ℕ) (E : C.Modules)
    (hE : ∀ x : C, ∃ U : C.Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj E ≅
        SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin d))))
    (N : C.Modules) (hN : Scheme.Modules.IsInvertible N) :
    let χ : C.Modules → ℤ := fun M =>
      (Module.finrank K (𝒰.sectionsOf c M).H0 : ℤ) -
        Module.finrank K (𝒰.sectionsOf c M).H1
    χ (N ⊗ E) = (d : ℤ) * (χ N - χ (𝟙_ C.Modules)) + χ E := by
  sorry
