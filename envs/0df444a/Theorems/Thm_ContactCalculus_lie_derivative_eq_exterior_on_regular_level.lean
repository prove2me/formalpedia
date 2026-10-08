-- Prove2me | Theorems.Thm_ContactCalculus_lie_derivative_eq_exterior_on_regular_level
-- name    : ContactCalculus.lie_derivative_eq_exterior_on_regular_level
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T09:47:25.707008+00:00
-- url     : https://prove2.me/theorems/0f300a92-69d3-497f-ad6f-242d9ed1d5da
-- title:
--   Cartan identity under annihilation on a regular level set
-- statement:
--   Let F be a smooth map between finite-dimensional real vector spaces. Let η and X be a differentiable one-form and vector field. Suppose η(X) vanishes on the zero level of F. At a point y of that level where DF(y) is surjective, every tangent vector v satisfies
--
--   $$ (\mathcal L_X\eta)_y(v)=(d\eta)_y(X(y),v). $$
--
--   Annihilation is required only on the level set; X need not be tangent to it. This is the restriction of Cartan’s formula to tangent directions.
-- source:
--   Geiges, Contact geometry, https://arxiv.org/abs/math/0307242, proof of Theorem 2.20, equation (2.1), printed p. 15. Regular-level formulation of Cartan’s formula under annihilation on the submanifold.

import Definitions.Def_GrayStability_Basic
import Theorems.Thm_ImplicitCalculus_tangent_map_of_mapsTo_regular_level
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open GrayStability
open scoped ContDiff Topology

theorem ContactCalculus.lie_derivative_eq_exterior_on_regular_level {n c : ℕ} (F : E n → E c)
    (hF : ContDiff ℝ ∞ F) (η : OneForm n) (X : E n → E n)
    (hη : Differentiable ℝ η) (hX : Differentiable ℝ X)
    (hz : ∀ z ∈ levelSet F, η z (X z) = 0)
    (y : E n) (hy : y ∈ levelSet F)
    (hD : Function.Surjective (fderiv ℝ F y))
    (v : E n) (hv : v ∈ tangentSpace F y) :
    lieDerivOneForm X η y v = extDerivOneForm η y (X y) v := by sorry
