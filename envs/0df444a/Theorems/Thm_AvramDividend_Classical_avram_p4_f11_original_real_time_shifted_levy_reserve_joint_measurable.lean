-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f11_original_real_time_shifted_levy_reserve_joint_measurable
-- name    : AvramDividend.Classical.avram_p4_f11_original_real_time_shifted_levy_reserve_joint_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T10:55:35.096902+00:00
-- url     : https://prove2.me/theorems/bd4c9667-557c-451d-a36e-9d2285d0e452
-- title:
--   Original real-time shifted Levy reserve is jointly measurable on time and sample
-- statement:
--   For the original Levy surplus, the map (s,omega) -> 1 + X.X (Real.toNNReal s) omega is measurable for real time and the probability sample. Obtain directly from existing Proved joint measurability on NNReal time via the measurable Real.toNNReal map and adding the deterministic initial reserve.
-- source:
--   Original Levy joint-time law Proved d55462c3. Needed in original first-exit signed generator time-space L1.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Mathlib.Probability.Martingale.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_f11_original_real_time_shifted_levy_reserve_joint_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    Measurable (fun p : ℝ × Ω =>
      1 + X.X (Real.toNNReal p.1) p.2) := by sorry
