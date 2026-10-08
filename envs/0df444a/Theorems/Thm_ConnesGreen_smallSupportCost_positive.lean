-- Prove2me | Theorems.Thm_ConnesGreen_smallSupportCost_positive
-- name    : ConnesGreen.smallSupportCost_positive
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T04:22:36.431027+00:00
-- url     : https://prove2.me/theorems/7d086888-5b78-4e63-a3d1-7cb86c031d77
-- title:
--   The original small-support loss cost is strictly positive
-- statement:
--   For the original gamma symbol gamma(r) = Re digamma(1/4+ir/2)-log(pi), let B=2 exp(6+|log(pi)|) and C=(gamma(B)-gamma(0)) 2B/pi+4 exp(1). Then C>0. This is the unchanged original support-loss constant; its positivity makes the ensuing explicit support radius well defined.
-- source:
--   monocap-tech/weil at f02a526d7c7fb8a43356376a2389d6f8afc08e2a; WeilDefect/Connes/SmallSupportPositivity.lean. Original native declarations and exact constant definition bodies unchanged.

import Definitions.Def_ConnesGreen_small_support_constants
import Definitions.Def_ConnesGreen_canonical_model
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect.ConnesNative Set
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

theorem ConnesGreen.smallSupportCost_positive : 0 < smallSupportCost := by sorry
