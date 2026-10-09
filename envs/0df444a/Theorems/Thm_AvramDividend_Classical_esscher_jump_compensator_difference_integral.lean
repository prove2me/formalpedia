-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_jump_compensator_difference_integral
-- name    : AvramDividend.Classical.esscher_jump_compensator_difference_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T16:15:05.803176+00:00
-- url     : https://prove2.me/theorems/df224fb4-62d6-4cb6-90ae-81033f6a6011
-- title:
--   Esscher-discounted jump compensator equals difference of two Lévy jump integrals
-- statement:
--   For a nonnegative jump-magnitude measure and any φ,s for which the compensation integrands at φ and φ+s are integrable, show ∫exp(-φz)(1-exp(-sz))dμ = J(φ+s)−J(φ), where J(t)=∫(1-exp(-tz))dμ. This follows pointwise from exp(-(φ+s)z)=exp(-φz)exp(-sz) and from linearity of the Bochner integral. It is the exact deterministic cancellation used with ψ(φ)=q to match the root-shifted geometric renewal transform against the q-scale-function transform.
-- source:
--   Pinned Mathlib Real.exp_add and MeasureTheory.integral_sub.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_jump_compensator_difference_integral
    (μ : Measure ℝ≥0) (φ s : ℝ)
    (hJφ : Integrable
      (fun z : ℝ≥0 => 1 - Real.exp (-(φ * (z : ℝ)))) μ)
    (hJplus : Integrable
      (fun z : ℝ≥0 => 1 - Real.exp (-((φ + s) * (z : ℝ)))) μ) :
    (∫ z : ℝ≥0,
      Real.exp (-(φ * (z : ℝ))) *
        (1 - Real.exp (-(s * (z : ℝ)))) ∂μ) =
      (∫ z : ℝ≥0, 1 - Real.exp (-((φ + s) * (z : ℝ))) ∂μ) -
        (∫ z : ℝ≥0, 1 - Real.exp (-(φ * (z : ℝ))) ∂μ) := by sorry
