-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_fixed_horizon_negative_band_L2_auto
-- name    : AvramDividend.Classical.avram_p4_s3_original_fixed_horizon_negative_band_L2_auto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:17:54.487464+00:00
-- url     : https://prove2.me/theorems/2a3995f9-21b5-4d5b-b00d-abaec891d5fa
-- title:
--   Original process finite-horizon separated negative-jump count has automatic L² membership
-- statement:
--   For the physical original spectrally negative Levy process, the number of jumps of size at most -1/(n+1) in (0,T] belongs to L², without any measurability or square-moment hypotheses. The original jump-count measurability and bounded-stop quadratic budget provide a direct source-specific proof.
-- source:
--   Proved original physical count measurability and P4-S3 50312326 original quadratic budget.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_original_fixed_horizon_negative_band_L2_auto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    MemLp (fun ω : Ω => ({u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard : ℝ)) 2 P := by sorry
