-- Prove2me | Theorems.Thm_ConnesGreen_weil_positive_small_support
-- name    : ConnesGreen.weil_positive_small_support
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T04:25:23.887322+00:00
-- url     : https://prove2.me/theorems/58b4988f-a0ec-4259-9ad3-532c138a35c1
-- title:
--   The full original Weil form is positive on the explicit small-support interval
-- statement:
--   For every real T with 0<=T<=R, where R is the unchanged original positiveSupportRadius, and every original smooth compactly supported test g supported in (-T,T), the full original Weil distribution on g convolved with its original involution has real part at least one half of the integral of |g| squared. All pole, prime and archimedean terms retain their original normalization. This unconditional local support result does not prove global Weil positivity or RH.
-- source:
--   monocap-tech/weil at f02a526d7c7fb8a43356376a2389d6f8afc08e2a; WeilDefect/Connes/SmallSupportPositivity.lean. Exact native declarations unchanged.

import Definitions.Def_ConnesGreen_small_support_constants
import Definitions.Def_ConnesGreen_canonical_model
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect.ConnesNative Set
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

theorem ConnesGreen.weil_positive_small_support (T : ℝ) (hT : 0 ≤ T)
    (hTr : T ≤ positiveSupportRadius) (g : ℝ → ℂ) (hg : SupportedTest T g) :
    (1 / 2 : ℝ) * (∫ s : ℝ, ‖g s‖ ^ 2) ≤
      (weilDistribution (conv g (starInv g))).re := by sorry
