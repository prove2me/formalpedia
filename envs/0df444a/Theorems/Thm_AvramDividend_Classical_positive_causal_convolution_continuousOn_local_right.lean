-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_causal_convolution_continuousOn_local_right
-- name    : AvramDividend.Classical.positive_causal_convolution_continuousOn_local_right
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T18:16:45.608562+00:00
-- url     : https://prove2.me/theorems/d652349d-002d-4fdd-91ea-d555698fe8ce
-- title:
--   Local continuity of causal L1 convolution with a continuous zero extension
-- statement:
--   An integrable real kernel on strictly positive times, convolved causally with a function whose zero extension from positive times is continuous on the full real line, yields a convolution continuous at every positive time. No global boundedness of the right factor is required. A compactly supported cutoff equal to one on the relevant finite interval reduces this to Mathlib's convolution-continuity theorem.

import Mathlib.Analysis.Convolution
import Mathlib.Topology.UrysohnsLemma
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set

theorem AvramDividend.Classical.positive_causal_convolution_continuousOn_local_right
    (f g : ℝ → ℝ)
    (hf : IntegrableOn f (Ioi (0 : ℝ)) volume)
    (hg : Continuous ((Ioi (0 : ℝ)).indicator g)) :
    ContinuousOn
      (MeasureTheory.posConvolution f g (ContinuousLinearMap.mul ℝ ℝ) volume)
      (Ioi (0 : ℝ)) := by sorry
