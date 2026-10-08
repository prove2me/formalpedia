-- Prove2me | Theorems.Thm_AvramDividend_Classical_exponential_hjb_verification_pair
-- name    : AvramDividend.Classical.exponential_hjb_verification_pair
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T06:28:07.621169+00:00
-- url     : https://prove2.me/theorems/0b758cde-8287-4a8d-a417-6792ea8443fb
-- title:
--   Exponential test functions satisfy both generator and gradient HJB verification inequalities
-- statement:
--   For θ≥1 and q≥ψ(θ), the exponential function w(x)=exp(θx) simultaneously satisfies (Γ−q)w(x)≤0 and w′(x)≥1 on all nonnegative reserves. This joins the two analytic inequalities in Proposition 4 local verification. It does not assert general stochastic Ito verification or cash-value optimality.
-- source:
--   The two child theorems exponential_generator_discount_supersolution and exponential_gradient_ge_one_of_ge_one_nonneg, both pinned to revision 0df444a3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.exponential_hjb_verification_pair
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ q : ℝ) (hθ : 1 ≤ θ) (hψ : X.ψ θ ≤ q) :
    ∀ x : ℝ, 0 ≤ x →
      (X.generator (fun y : ℝ => Real.exp (θ * y)) x -
        q * Real.exp (θ * x) ≤ 0) ∧
      (1 ≤ deriv (fun y : ℝ => Real.exp (θ * y)) x) := by sorry
