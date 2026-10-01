-- Prove2me | Theorems.Thm_Apery_real_bound
-- name    : Apery.real_bound
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-01T11:09:44.385696+00:00
-- url     : https://prove2.me/theorems/35bd2c2c-ff9a-4220-a70d-3b4cc8d015b0
-- title:
--   Analytic upper bound for the Hankel polynomial value
-- statement:
--   For every positive natural number $n$, with $K_n=40n$ and $U=-2733991/2000000$,
--   $$0<F_n(z_5),\qquad\log F_n(z_5)\le UK_n^2+27K_n\log K_n+200K_n.$$
--   This is the repository's analytic estimate, including its explicit lower-order terms. Together with the arithmetic normalization bound, it gives the negative quadratic exponent needed for irrationality.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/MainEstimate.lean#L31-L37; https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/RealBound.lean#L88

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceConstants
import Definitions.Def_Zeta5_SourceValue

open Polynomial Filter Topology MeasureTheory

namespace Apery

theorem real_bound (n : ℕ) (hn : 0 < n) :
    0 < aeval zeta5 (F n) ∧
      Real.log (aeval zeta5 (F n)) ≤
        (U : ℝ) * Kr n ^ 2 + 27 * Kr n * Real.log (Kr n) + 200 * Kr n := by sorry

end Apery
