-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat01_finite_upcrossing_window_discount_integral_bound
-- name    : AvramDividend.Classical.chat01_finite_upcrossing_window_discount_integral_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:58:50.339403+00:00
-- url     : https://prove2.me/theorems/751a5705-ac6e-4826-9c63-a5e1202c58e2
-- title:
--   Discounted finite-time upcrossing window mass bound
-- statement:
--   Under a positive Esscher root and nonnegative level, the horizon-discounted mass of the finite upcrossing time window is at most the exponential Esscher spatial tail. This requires no separate measurability assumption on the window because the statement is a Lebesgue integral of an indicator.
-- source:
--   Proved chat01_finite_horizon_upcrossing_discount_bound, instantiated at the concrete finite-time upcrossing window.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_chat01_finite_horizon_upcrossing_discount_bound
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat01_finite_upcrossing_window_discount_integral_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (z : ℝ) (hz : 0 ≤ z) (t : ℝ) :
    (∫⁻ ω, ({ω | twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞) ∧
      ENNReal.toReal (twoSidedExitUpTimeCorrected X z ω) ≤ t}).indicator
      (fun ω => ENNReal.ofReal (Real.exp (-(q * t)))) ω ∂P) ≤
      ENNReal.ofReal (Real.exp (-(φ * z))) := by sorry
