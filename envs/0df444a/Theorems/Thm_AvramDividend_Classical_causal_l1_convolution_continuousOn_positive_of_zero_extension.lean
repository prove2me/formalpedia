-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_continuousOn_positive_of_zero_extension
-- name    : AvramDividend.Classical.causal_l1_convolution_continuousOn_positive_of_zero_extension
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T06:49:11.633539+00:00
-- url     : https://prove2.me/theorems/9284d866-1330-4363-9374-439ecdb43640
-- title:
--   Positive-time continuity of an L1 causal integral from zero-extension continuity
-- statement:
--   For a real kernel K integrable on positive times and a right factor V whose zero extension from (0,∞) is globally continuous, the causal set-integral x↦∫_(0,x]K(x−s)V(s)ds is continuous for x>0. Apply the already Proved local-right positive convolution continuity lemma, and identify its posConvolution expression with the Ioc causal integral via the exact time-reversal theorem. This bridges existing regularity results to the concrete Volterra operator.

import Mathlib.Analysis.Convolution
import Theorems.Thm_AvramDividend_Classical_positive_causal_convolution_continuousOn_local_right
import Theorems.Thm_AvramDividend_Classical_positive_causal_integral_eq_posConvolution
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_l1_convolution_continuousOn_positive_of_zero_extension
    (K V : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hV : Continuous ((Ioi (0 : ℝ)).indicator V)) :
    ContinuousOn (fun x : ℝ =>
      ∫ s in Ioc (0 : ℝ) x, K (x - s) * V s ∂volume)
      (Ioi (0 : ℝ)) := by sorry
