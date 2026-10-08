-- Prove2me | Theorems.Thm_ConnesGreen_positiveSupportRadius_positive
-- name    : ConnesGreen.positiveSupportRadius_positive
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T04:25:24.419348+00:00
-- url     : https://prove2.me/theorems/56799495-69f0-46c6-8973-d2c714cfbe4a
-- title:
--   The original explicit Weil positivity support radius is nonzero
-- statement:
--   Let C be the original small-support cost and R=min(log(2)/2,min(1,1/(2C))). Then R>0. Thus the original small-support theorem applies on a nonempty interval. This does not identify the intended critical endpoint.
-- source:
--   monocap-tech/weil at f02a526d7c7fb8a43356376a2389d6f8afc08e2a; WeilDefect/Connes/SmallSupportPositivity.lean. Exact native declarations unchanged.

import Definitions.Def_ConnesGreen_small_support_constants
import Definitions.Def_ConnesGreen_canonical_model
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect.ConnesNative Set
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

theorem ConnesGreen.positiveSupportRadius_positive : 0 < positiveSupportRadius := by sorry
