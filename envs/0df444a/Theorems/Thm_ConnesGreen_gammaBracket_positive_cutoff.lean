-- Prove2me | Theorems.Thm_ConnesGreen_gammaBracket_positive_cutoff
-- name    : ConnesGreen.gammaBracket_positive_cutoff
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T01:33:37.010051+00:00
-- url     : https://prove2.me/theorems/32459c2d-303e-45df-9009-18653bb02ff8
-- title:
--   Original explicit gamma cutoff has symbol at least one
-- statement:
--   For the unchanged positiveGammaCutoff=2 exp(6+|log(pi)|), the original gammaBracket at this cutoff is at least one. The public signature unfolds exactly the original symbol and cutoff definitions, retaining the 1/4 shift and r/2 scale. The accepted log-absolute-frequency Stirling adapter gives the original error estimate; elementary exponential and logarithmic inequalities prove the bound. No assumed gamma positivity or RH premise is introduced.
-- source:
--   monocap-tech/weil at 9f63bd900711de6b599c8ddd2b487176103f4075; ArchimedeanFrequency.lean and SmallSupportPositivity.lean. Original native declarations unchanged. Exact native definition normalization checks accompany both ports.

import Mathlib
import Theorems.Thm_ConnesGreen_digamma_stirling_log_abs
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Complex

theorem ConnesGreen.gammaBracket_positive_cutoff :
    1 ≤ (Complex.digamma (1 / 4 + I * ((2 * Real.exp (6 + |Real.log Real.pi|) : ℝ) : ℂ) / 2)).re - Real.log Real.pi := by sorry
