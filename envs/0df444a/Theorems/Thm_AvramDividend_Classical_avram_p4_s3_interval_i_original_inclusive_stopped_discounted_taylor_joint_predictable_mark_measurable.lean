-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_i_original_inclusive_stopped_discounted_taylor_joint_predictable_mark_measurable
-- name    : AvramDividend.Classical.avram_p4_s3_interval_i_original_inclusive_stopped_discounted_taylor_joint_predictable_mark_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:23:48.933626+00:00
-- url     : https://prove2.me/theorems/a1d74dd5-9c86-47c6-899d-eede77ef7d99
-- title:
--   Original stopped discounted nonlinear Ito-Meyer integrand jointly measurable in physical predictable time-path and real Lévy mark
-- statement:
--   The same original spectrally negative Lévy path X, dividend strategy D, stopped time τ and right-continuous filtration yield a fully jointly measurable nonlinear Taylor kernel on predictable time-path × genuine real Lévy marks, including the inclusive stopping survival and exponential discount. No synthetic random measures and no hidden integrability premise.
-- source:
--   Combine public original physical joint Taylor mark predictable measurability, source original inclusive survival predictability, and a deterministic continuous discount. Lift time-path measurability to the product with original real Lévy marks and multiply the three exact factors.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_i_original_physical_prejump_taylor_joint_predictable_mark_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_inclusiveSurvival_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_strongAdapted_leftContinuous_predictable
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_interval_i_original_inclusive_stopped_discounted_taylor_joint_predictable_mark_measurable
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
          ((fun y : ℝ => w (y + p.2) - w y - p.2 * deriv w y)
            (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.1.2 -
                rightLimit D s p.1.2) p.1.1))) := by sorry
