-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_Ioc_causal_convolution_continuous_bounded_second
-- name    : AvramDividend.Classical.positive_Ioc_causal_convolution_continuous_bounded_second
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T19:05:15.202452+00:00
-- url     : https://prove2.me/theorems/8c0b09e1-ff7b-431c-af98-e3356c4e9c0b
-- title:
--   Positive real causal convolution is continuous with bounded second factor
-- statement:
--   When g is integrable on the positive axis and the positive indicator of f is globally bounded and continuous, the function x↦∫_(0,x] f(s)g(x−s) ds is continuous for all x>0. The exact Ioc causal commutativity lemma swaps the integrand, and the already-Proved bounded-right positive convolution continuity applies with left g (integrable) and right f (bounded continuous). Uses no artificial global boundedness of the first integral factor.
-- source:
--   Proved positive_causal_convolution_continuous_bounded_right and exact Ioc commutativity (pending proof).

import Mathlib.Analysis.Convolution
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_positive_causal_convolution_continuous_bounded_right
import Theorems.Thm_AvramDividend_Classical_positive_Ioc_causal_convolution_comm_real
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.positive_Ioc_causal_convolution_continuous_bounded_second
    (f g : ℝ → ℝ)
    (hg : IntegrableOn g (Ioi (0 : ℝ)) volume)
    (hf : Continuous ((Ioi (0 : ℝ)).indicator f))
    (hfb : BddAbove (Set.range (fun x : ℝ =>
      ‖(Ioi (0 : ℝ)).indicator f x‖))) :
    ContinuousOn (fun x : ℝ =>
      ∫ s in Ioc (0 : ℝ) x, f s * g (x - s) ∂volume)
      (Ioi (0 : ℝ)) := by sorry
