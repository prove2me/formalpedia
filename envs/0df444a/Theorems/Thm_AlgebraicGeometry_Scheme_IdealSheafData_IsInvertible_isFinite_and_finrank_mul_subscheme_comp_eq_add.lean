-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isFinite_and_finrank_mul_subscheme_comp_eq_add
-- name    : AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.isFinite_and_finrank_mul_subscheme_comp_eq_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/77649b73-6f7f-5a78-9efe-d8f2ed259dab
-- title:
--   Additivity of finrank for products of invertible ideal sheaves
-- statement:
--   Let $\kappa$ be a field, $X$ a scheme, and $f : X \to \operatorname{Spec} \kappa$ a proper morphism. Let $\mathcal{V}$ be a two-affine open cover of $X$, that is, a pair of opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ such that $U_0$, $U_1$ and $U_0 \cap U_1$ are all affine. Let $I$ and $J$ be ideal sheaf data on $X$, each satisfying the invertibility predicate `IsInvertible`: for every point $x$ of $X$ there are an affine open $U$ and a section $f \in \Gamma(X, U)$ with $x \in X_f$, together with a non-zero-divisor $g$ of $\Gamma(X, X_f)$ such that the ideal cut out by the sheaf data on the affine basic open $X_f$ is $(g)$. Assume further that the composites $V(I) \hookrightarrow X \to \operatorname{Spec} \kappa$ and $V(J) \hookrightarrow X \to \operatorname{Spec} \kappa$ of the closed immersions of the associated closed subschemes with $f$ are finite morphisms, and let $y$ be a point of $\operatorname{Spec} \kappa$. Then the composite $V(IJ) \hookrightarrow X \to \operatorname{Spec} \kappa$ for the product ideal sheaf $I \cdot J$ is also finite, and its fibre rank at $y$ is the sum of those of $I$ and $J$: $\operatorname{finrank}_y(V(IJ) \to \operatorname{Spec}\kappa) = \operatorname{finrank}_y(V(I) \to \operatorname{Spec}\kappa) + \operatorname{finrank}_y(V(J) \to \operatorname{Spec}\kappa)$.
--
--   This is the additivity of the degree (colength) of effective Cartier divisors of finite support on a proper scheme over a field, in the form $\dim_\kappa \Gamma(\mathcal{O}_X/IJ) = \dim_\kappa \Gamma(\mathcal{O}_X/I) + \dim_\kappa \Gamma(\mathcal{O}_X/J)$, and it underlies the group law on degrees in the relative Picard formalism used for curves. It is cited in the construction of the relative Picard functor and in the computation of Euler characteristics of tensor products of invertible modules with kernels of ideal sheaves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isFinite_and_finrank_mul_subscheme_comp_eq_add.lean

import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.isFinite_and_finrank_mul_subscheme_comp_eq_add
    {κ : Type u} [Field κ] {X : Scheme.{u}} (f : X ⟶ Spec (.of κ)) [IsProper f]
    (𝒱 : X.TwoAffineOpenCover) {I J : X.IdealSheafData} (hI : I.IsInvertible)
    (hJ : J.IsInvertible) [IsFinite (I.subschemeι ≫ f)] [IsFinite (J.subschemeι ≫ f)]
    (y : Spec (.of κ)) :
    IsFinite ((I * J).subschemeι ≫ f) ∧
      ((I * J).subschemeι ≫ f).finrank y =
        (I.subschemeι ≫ f).finrank y + (J.subschemeι ≫ f).finrank y := by sorry
