-- Prove2me | Theorems.Thm_BroughanRH_schoenfeldInteger
-- name    : BroughanRH.schoenfeldInteger
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:29:10.437794+00:00
-- url     : https://prove2.me/theorems/5d8704d4-a5af-421d-8f77-b63a5454ccfb
-- title:
--   A positive-integer Chebyshev test
-- statement:
--   Every integer $n\ge600$ satisfies the strict Chebyshev estimate used in the reduction to arithmetic.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, III §11.3. https://doi.org/10.1017/9781009384780

import Mathlib

namespace BroughanRH

theorem schoenfeldInteger :
    ∀ n : ℕ, 600 ≤ n → |Chebyshev.psi n - (n : ℝ)| < Real.sqrt n * (Real.log n)^2 := by sorry

end BroughanRH
