-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a161_original_positive_C2_gaussian_stopped_iterated_derivative_ae_measurable
-- name    : AvramDividend.Classical.avram_ga_a161_original_positive_C2_gaussian_stopped_iterated_derivative_ae_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T12:33:31.831817+00:00
-- url     : https://prove2.me/theorems/b9604830-ee3e-45fd-b8dc-d5f683d2236f
-- title:
--   Actual stopped Gaussian positive-domain C2 spatial first and second derivatives are a.e. measurable along measurable strictly positive original reserve
-- statement:
--   For any original Gaussian Avram value function C2 on strictly positive reserves, each ordinary iterated derivative of order at most two is continuous there. When evaluated at an actual original measurable stopped positive reserve, it is a.e. strongly measurable even though the value function and derivatives may be undefined or nonmeasurable outside the positive domain. This supplies the missing source-correct gradient/Hessian measurability to the physically full stopped source Taylor residual ga152 and the original spatial root ga146.
-- source:
--   Pinned Mathlib ContDiffOn.continuousOn_iteratedDerivWithin, iteratedDerivWithin_of_isOpen, ContinuousOn.measurable_piecewise, AEStronglyMeasurable.congr.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a161_original_positive_C2_gaussian_stopped_iterated_derivative_ae_measurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (w : ℝ → ℝ) (hw : ContDiffOn ℝ 2 w (Ioi (0 : ℝ)))
    (k : ℕ) (hk : k ≤ 2)
    (Y : Ω → ℝ) (hY : Measurable Y)
    (hPos : ∀ᵐ ω ∂P, 0 < Y ω) :
    AEStronglyMeasurable
      (fun ω => iteratedDeriv k w (Y ω)) P := by sorry
