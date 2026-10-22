-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_tilt_C1_of_positive_integrated_excursion_tail
-- name    : AvramDividend.Classical.esscher_tilt_C1_of_positive_integrated_excursion_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T23:20:38.923922+00:00
-- url     : https://prove2.me/theorems/3042870c-584d-498f-b146-31cbee557dcf
-- title:
--   Esscher-tilted C1 regularity from a locally continuous excursion integral
-- statement:
--   Given a positive anchor a, a tail function T continuous on positive levels and an exponential excursion-integral representation for W on positive levels, the Esscher transform V(x)=exp(-φx)W(x) is continuously differentiable on the positive axis. The tail may diverge at zero. This composes independently proved FTC regularity and Esscher-tilt smoothness, and is intended for the Gaussian and infinite small-jump branches of the unbounded-variation theorem.
-- source:
--   Deterministic consequence of the Proved excursion integral FTC bridge and Esscher smoothness transfer; applicable to Chan, Kyprianou and Savov (2009), arXiv:0903.1467v1, equation (5).

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Theorems.Thm_AvramDividend_Classical_contDiffOn_one_of_positive_integrated_excursion_tail
import Theorems.Thm_AvramDividend_Classical_esscher_tilt_contDiffOn_one_of_scale_contDiffOn_one
open AvramDividend.Classical Set MeasureTheory intervalIntegral

theorem AvramDividend.Classical.esscher_tilt_C1_of_positive_integrated_excursion_tail
    (T W V : ℝ → ℝ) (a c φ : ℝ) (ha : 0 < a)
    (hT : ContinuousOn T (Ioi (0 : ℝ)))
    (hW : ∀ x : ℝ, 0 < x →
      W x = c * Real.exp (∫ t in a..x, T t))
    (hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x) :
    ContDiffOn ℝ 1 V (Ioi (0 : ℝ)) := by sorry
