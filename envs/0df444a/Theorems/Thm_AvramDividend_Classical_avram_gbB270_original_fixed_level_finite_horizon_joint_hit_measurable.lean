-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB270_original_fixed_level_finite_horizon_joint_hit_measurable
-- name    : AvramDividend.Classical.avram_gbB270_original_fixed_level_finite_horizon_joint_hit_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T22:45:43.750288+00:00
-- url     : https://prove2.me/theorems/26f37d7b-f970-4bad-8ebc-765d00a6c5a5
-- title:
--   Original fixed-level reserve hit event jointly measurable over finite horizon
-- statement:
--   For every original Levy source and adapted dividend strategy, the event in real time and original outcome where time is strictly between zero and a deterministic finite horizon and original postpayment reserve equals any prescribed fixed spatial level is jointly measurable. This follows from the original reserve joint measurability lemma B269 and measurable conversion from real physical time to nonnegative time. This supplies the Tonelli hypothesis for B100 fixed-level original Gaussian occupation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB269_original_postpayment_reserve_joint_time_sample_measurable

open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB270_original_fixed_level_finite_horizon_joint_hit_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (n : ℕ) :
    MeasurableSet {z : ℝ × Ω |
      0 < z.1 ∧ z.1 < (n : ℝ) ∧
        x + X.X (Real.toNNReal z.1) z.2 -
          rightLimit D (Real.toNNReal z.1) z.2 = b} := by sorry
