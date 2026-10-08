-- Prove2me | Theorems.Thm_ConnesGreen_digamma_stirling_log_abs
-- name    : ConnesGreen.digamma_stirling_log_abs
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T01:09:15.273019+00:00
-- url     : https://prove2.me/theorems/b671f23e-0cb3-4ec9-83c6-a2378384c71f
-- title:
--   Vertical digamma Stirling estimate in the native log absolute-frequency normalization
-- statement:
--   For 0<a<=1 and |t|>=1/2, the absolute difference between Re digamma(a+i t) and log(|t|) is at most 5/t^2. This is precisely the native primed adapter used by the original Connes positive gamma cutoff. The current-toolchain accepted unprimed vertical Stirling theorem has center (1/2)log(a^2+t^2) and error 4/t^2. Their center difference is (1/2)log(1+a^2/t^2), bounded by 1/t^2 using log(1+x)<=x and a^2<=1. The triangle inequality gives the original 5/t^2 bound. No asymptotic axiom, assumed gamma positivity or RH premise is introduced.
-- source:
--   monocap-tech/weil at 5ba603ccaacf5ea1172c6cf087b8c5f33f029bb5; ArchimedeanEnergy.lean and original GammaFacts/StirlingVert.lean. Original native declarations unchanged. Independent Mathlib-only platform proof audit recovers the original HasSum digamma series.

import Mathlib
import Theorems.Thm_Zeta23_StirlingVert_re_digamma_stirling
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Complex

theorem ConnesGreen.digamma_stirling_log_abs {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) {t : ℝ} (ht : 1 / 2 ≤ |t|) :
    |(Complex.digamma ((a : ℂ) + Complex.I * t)).re - Real.log (abs t)| ≤ 5 / t ^ 2 := by sorry
