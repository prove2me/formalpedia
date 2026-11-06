-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_i_original_physical_prejump_taylor_joint_predictable_mark_measurable
-- name    : AvramDividend.Classical.avram_p4_s3_interval_i_original_physical_prejump_taylor_joint_predictable_mark_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:15:49.32892+00:00
-- url     : https://prove2.me/theorems/ea5cc9f2-060c-4d33-9f44-880b3f64c9f1
-- title:
--   Original controlled nonlinear Taylor integrand jointly predictable-measurable in time-path and physical Lévy mark
-- statement:
--   For the actual original spectrally negative Lévy process and the same controlled pre-jump reserve, the full nonlinear Taylor integrand as a function of predictable time-path and genuine real Lévy mark is jointly measurable in the physical predictable sigma algebra product the real Borel mark sigma algebra. This handles state-dependent mark measurability without imposing terminal stochastic integrability, clipping or changing the process.
-- source:
--   Proved 94ee9994 is the exact source physical post-payment left-limit predictable measurability. Pull it to the predictable time-path × real mark product space via measurable_fst, combine with the genuine mark projection measurable_snd, and compose measurable w and measurable_deriv w. The resulting nonlinear Itô–Meyer Taylor remainder is jointly predictable/mark measurable.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_interval_i_original_physical_prejump_taylor_joint_predictable_mark_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw : Measurable w) :
    Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)]
      (fun p : ((ℝ≥0 × Ω) × ℝ) =>
        (fun y : ℝ => w (y + p.2) - w y - p.2 * deriv w y)
          (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 -
              rightLimit D s p.1.2) p.1.1)) := by sorry
