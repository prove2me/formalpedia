-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_i_original_inclusive_stopped_discounted_truncated_compensation_taylor_joint_predictable_mark_measurable
-- name    : AvramDividend.Classical.avram_p4_s3_interval_i_original_inclusive_stopped_discounted_truncated_compensation_taylor_joint_predictable_mark_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:34:19.379265+00:00
-- url     : https://prove2.me/theorems/04699643-146b-4a9e-81fc-f6fa209e9c4a
-- title:
--   Exact physical original -1 truncated Lévy compensation stopped discounted nonlinear Taylor kernel jointly predictable/mark measurable
-- statement:
--   The same original spectrally negative Lévy process X, physical strategy D and actual stop τ yield a jointly predictable/real-mark measurable Itô–Meyer jump kernel with correct derivative compensation only for small negative marks z>-1, including exponential discount and the inclusive stopped survival indicator. No independent process or hidden large-negative-jump second moment.
-- source:
--   Compose original joint physical mark measurability with actual Lévy compensation cutoff -1, genuine inclusive stopped survival predictability and deterministic continuous exponential discount. Pull the two predictable factors to the real-mark product and multiply with the original state-and-mark nonlinear Taylor generator.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_i_original_truncated_compensation_taylor_joint_predictable_mark_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_inclusiveSurvival_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_strongAdapted_leftContinuous_predictable
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_interval_i_original_inclusive_stopped_discounted_truncated_compensation_taylor_joint_predictable_mark_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw : Measurable w) (q : ℝ)
    (τ : Ω → ℝ≥0∞)
    (hτ : IsStoppingTime 𝓕.rightCont τ) :
    Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)]
      (fun p : ((ℝ≥0 × Ω) × ℝ) =>
        ((if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then (1 : ℝ) else 0) *
          Real.exp (-(q * (p.1.1 : ℝ)))) *
          ((fun y : ℝ => w (y + p.2) - w y -
            (if -1 < p.2 then p.2 * deriv w y else 0))
            (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.1.2 -
                rightLimit D s p.1.2) p.1.1))) := by sorry
