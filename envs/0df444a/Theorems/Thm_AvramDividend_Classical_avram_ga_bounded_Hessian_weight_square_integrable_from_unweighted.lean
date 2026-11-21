-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_bounded_Hessian_weight_square_integrable_from_unweighted
-- name    : AvramDividend.Classical.avram_ga_bounded_Hessian_weight_square_integrable_from_unweighted
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T00:34:48.284523+00:00
-- url     : https://prove2.me/theorems/20c41376-0bba-4724-868a-b76a5e22857f
-- title:
--   Original Gaussian stopped Hessian weighted quadratic-square integrability from bounded coefficient and unweighted fourth moment
-- statement:
--   Given an integrable square R² of the authentic centred Gaussian squared increment, an almost-everywhere strongly measurable weighted square (H R)², and a uniform random Hessian coefficient bound |H|≤K, the weighted square is integrable. This supplies the previously explicit hHI prerequisite of the original weighted Gaussian physical-cell L2 bound from the authentic unweighted gb41 fourth moment and the Proved predictable masked Hessian boundedness.
-- source:
--   Close the integrability prerequisite in original physical finite-cap Gaussian Hermite second-channel L2 estimates without invoking independence or anticipative full-cell masks.

import Mathlib
open MeasureTheory Filter
noncomputable section

theorem AvramDividend.Classical.avram_ga_bounded_Hessian_weight_square_integrable_from_unweighted
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (H R : Ω → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hBound : ∀ ω, |H ω| ≤ K)
    (hR : Integrable (fun ω => R ω ^ 2) P)
    (hMeas : AEStronglyMeasurable (fun ω => (H ω * R ω) ^ 2) P) :
    Integrable (fun ω => (H ω * R ω) ^ 2) P := by sorry
