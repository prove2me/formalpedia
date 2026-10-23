-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_positive_euler_degree_multiplier_of_finite_surjective
-- name    : AlgebraicGeometry.SmoothProperCurve.exists_positive_euler_degree_multiplier_of_finite_surjective
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-13T16:40:28.992983+00:00
-- url     : https://prove2.me/theorems/fe7590dd-9af2-454f-aef3-0a57465c8f6b
-- title:
--   A positive degree multiplier for finite surjective maps of smooth proper curves
-- statement:
--   Let $K$ be a field, let $C$ and $D$ be smooth proper integral curves over $K$, and let $g:D\to C$ be a finite surjective $K$-morphism. Choose covers $\mathcal U$ and $\mathcal V$ of $C$ and $D$ by two affine opens. For a coherent sheaf $N$, write
--
--   $$\chi_C(N)=\dim_K H^0(C,N)-\dim_K H^1(C,N),\qquad
--   \chi_D(N)=\dim_K H^0(D,N)-\dim_K H^1(D,N).$$
--
--   There is a positive integer $d$, independent of the invertible sheaf $L$ on $C$, such that
--
--   $$\chi_D(g^*L)-\chi_D(\mathcal O_D)
--   =d\bigl(\chi_C(L)-\chi_C(\mathcal O_C)\bigr).$$
--
--   The multiplier may be taken to be the degree of the function-field extension $K(D)/K(C)$. The statement allows inseparable maps and does not require $K$ to be algebraically closed. It supplies the integer degree identity used to compare numerical triviality across finite curve covers.
--
--   **Formalization Note.** The Euler characteristics use the existing two-chart Cech section modules associated to the specified covers. The formal conclusion asks for a single positive integer multiplier valid for all invertible sheaves.
-- source:
--   Stacks Project, Lemma 33.44.11 (https://stacks.math.columbia.edu/tag/0AYZ), with degree defined by Definition 33.44.1 in https://stacks.math.columbia.edu/tag/0AYQ. Specialize the locally free sheaf to an invertible sheaf on smooth proper integral curves; a finite surjective curve map is nonconstant. The positive multiplier is the function-field degree, chosen before the sheaf. Cech cohomology for the two-affine-open cover computes the displayed Euler characteristics, so this is the concrete Cech formulation of the source formula.

import Definitions.Def_AlgebraicGeometry_CurveDegreeTests
import Mathlib.AlgebraicGeometry.Morphisms.Finite

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u

theorem AlgebraicGeometry.SmoothProperCurve.exists_positive_euler_degree_multiplier_of_finite_surjective
    (K : Type u) [Field K] {C D : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) (δ : D ⟶ Spec (.of K))
    [IsIntegral C] [IsIntegral D] [IsProper c] [IsProper δ]
    [SmoothOfRelativeDimension 1 c] [SmoothOfRelativeDimension 1 δ]
    (g : D ⟶ C) [IsFinite g] [Surjective g] (hg : g ≫ c = δ)
    (𝒰 : C.TwoAffineOpenCover) (𝒱 : D.TwoAffineOpenCover) :
    let χC : C.Modules → ℤ := fun N =>
      (Module.finrank K (𝒰.sectionsOf c N).H0 : ℤ) -
        Module.finrank K (𝒰.sectionsOf c N).H1
    let χD : D.Modules → ℤ := fun N =>
      (Module.finrank K (𝒱.sectionsOf δ N).H0 : ℤ) -
        Module.finrank K (𝒱.sectionsOf δ N).H1
    ∃ d : ℕ, 0 < d ∧ ∀ N : C.Modules, Scheme.Modules.IsInvertible N →
      χD ((Scheme.Modules.pullback g).obj N) - χD (𝟙_ D.Modules) =
        (d : ℤ) * (χC N - χC (𝟙_ C.Modules)) := by
  sorry
