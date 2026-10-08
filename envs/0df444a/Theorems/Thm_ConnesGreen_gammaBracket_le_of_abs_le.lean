-- Prove2me | Theorems.Thm_ConnesGreen_gammaBracket_le_of_abs_le
-- name    : ConnesGreen.gammaBracket_le_of_abs_le
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T01:33:23.63273+00:00
-- url     : https://prove2.me/theorems/59a822e2-e8c8-4945-9b6c-6de96668df75
-- title:
--   Original gamma symbol increases with absolute frequency
-- statement:
--   For B>=0 and B<=|r|, the original gammaBracket(B) is at most gammaBracket(r), with gammaBracket(t)=Re digamma(1/4+i t/2)-log(pi). The public signature unfolds only this original definition. Accepted real digamma monotonicity on the nonnegative vertical coordinate, together with conjugation symmetry proved directly from the original Gamma function, supplies this exact bound. No gamma lower-bound hypothesis, endpoint inequality or RH premise is introduced.
-- source:
--   monocap-tech/weil at 9f63bd900711de6b599c8ddd2b487176103f4075; ArchimedeanFrequency.lean and SmallSupportPositivity.lean. Original native declarations unchanged. Exact native definition normalization checks accompany both ports.

import Mathlib
import Theorems.Thm_Zeta23_MuFields_re_digamma_mono
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Complex

theorem ConnesGreen.gammaBracket_le_of_abs_le (B r : ℝ) (hB : 0 ≤ B) (hBr : B ≤ |r|) :
    (Complex.digamma (1 / 4 + I * B / 2)).re - Real.log Real.pi ≤
      (Complex.digamma (1 / 4 + I * r / 2)).re - Real.log Real.pi := by sorry
