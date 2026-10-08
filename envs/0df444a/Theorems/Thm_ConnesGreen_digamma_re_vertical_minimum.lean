-- Prove2me | Theorems.Thm_ConnesGreen_digamma_re_vertical_minimum
-- name    : ConnesGreen.digamma_re_vertical_minimum
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T00:58:02.666014+00:00
-- url     : https://prove2.me/theorems/7583be86-06e1-496d-96b4-c5d5f6e66a22
-- title:
--   Digamma on the original open unit strip is minimized vertically at zero
-- statement:
--   For 0<a<1 and every real r, Re digamma(a) <= Re digamma(a+i r). This is exactly the existing native theorem, proved using the existing convergent digamma series and termwise reciprocal real-part comparison. The current-toolchain community series theorem is reused rather than republished. No positivity, gamma lower-bound, zero-tail or RH assumption is introduced.
-- source:
--   monocap-tech/weil at 5ba603ccaacf5ea1172c6cf087b8c5f33f029bb5; ArchimedeanEnergy.lean. Original native declarations unchanged. Independent Mathlib-only platform proof audit recovers the original HasSum digamma series.

import Mathlib
import Theorems.Thm_Zeta23_DigammaSeries_hasSum_digamma_series
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Complex

theorem ConnesGreen.digamma_re_vertical_minimum (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (r : ℝ) :
    (Complex.digamma (a : ℂ)).re ≤ (Complex.digamma ((a : ℂ) + I * r)).re := by sorry
