-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva21_closed_cap_continuous_kernel_mask_measurable
-- name    : AvramDividend.Classical.avram_bva21_closed_cap_continuous_kernel_mask_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:09:37.01107+00:00
-- url     : https://prove2.me/theorems/2a89ef26-aea3-412c-bc16-f5adb7c0cdd8
-- title:
--   Closed-cap continuous negative-mark kernel has measurable zero extension along measurable physical reserve
-- statement:
--   The original negative-mark compensator rate ψ is continuous on the inclusive compact reserve cap by the parent's finite-mark kernel uniform continuity hypothesis. For any measurable original physical prepayment reserve U, its cap-masked value ψ(U t) is measurable despite ψ being unrestricted outside the cap, because the extension by zero across the Borel cap is measurable by continuous-on-piecewise. This removes the need to prove global ψ measurability in the source-K time-integral bridge.
-- source:
--   Essential original finite-cap negative-mark time-kernel measurability needed for 7ccc2a1a from its exact uniform-continuity hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva21_closed_cap_continuous_kernel_mask_measurable
    (C : ℝ≥0∞) (ψ : ℝ → ℝ)
    (hcont : ContinuousOn ψ
      {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C})
    (U : ℝ≥0 → ℝ) (hU : Measurable U) :
    Measurable (fun t : ℝ≥0 =>
      if 0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C then ψ (U t) else 0) := by sorry
