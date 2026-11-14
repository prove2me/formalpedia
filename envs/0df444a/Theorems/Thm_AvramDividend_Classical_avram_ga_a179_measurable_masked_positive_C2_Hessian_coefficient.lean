-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a179_measurable_masked_positive_C2_Hessian_coefficient
-- name    : AvramDividend.Classical.avram_ga_a179_measurable_masked_positive_C2_Hessian_coefficient
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T15:38:55.920803+00:00
-- url     : https://prove2.me/theorems/3a8ca473-7021-45cc-89bb-7fa473d0c8f1
-- title:
--   Gaussian stopped masked C2 Hessian coefficient a.e. strongly measurable on a positive active source domain
-- statement:
--   For a measurable sample-dependent active-cell mask, a source reserve that is strictly positive almost surely on that mask and a function twice differentiable on positive reserves, the finite physical-source Hessian coefficient extended by zero outside the mask is almost everywhere strongly measurable. This applies to the genuine stopped Gaussian source X and dividend right-limit and supplies ga_a178's measurability prerequisite for original a150.
-- source:
--   Proved a161 positive C2 a.e. derivative measurability and finite measurable stopping mask.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a161_original_positive_C2_gaussian_stopped_iterated_derivative_ae_measurable
open MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a179_measurable_masked_positive_C2_Hessian_coefficient
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (w : ℝ → ℝ) (hw : ContDiffOn ℝ 2 w (Ioi (0 : ℝ)))
    (A : Ω → Prop) [DecidablePred A]
    (hA : MeasurableSet {ω : Ω | A ω})
    (Y : Ω → ℝ) (hY : Measurable Y)
    (hPos : ∀ᵐ ω ∂P, A ω → 0 < Y ω)
    (E : ℝ) :
    AEStronglyMeasurable (fun ω =>
      if A ω then E * iteratedDeriv 2 w (Y ω) else 0) P := by sorry
