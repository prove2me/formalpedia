-- Prove2me | Theorems.Thm_BroughanRH_liouvilleSum
-- name    : BroughanRH.liouvilleSum
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:12:12.227651+00:00
-- url     : https://prove2.me/theorems/32a0f491-c297-480f-8501-0be9d93b8dc0
-- title:
--   Square-root cancellation of Liouville sums
-- statement:
--   The summatory Liouville function is $O_\varepsilon(N^{1/2+\varepsilon})$ for each $\varepsilon>0$.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, I §4.4. https://doi.org/10.1017/9781108178228

import Mathlib

namespace BroughanRH

theorem liouvilleSum :
    ∀ ε : ℝ, 0 < ε → Asymptotics.IsBigO Filter.atTop (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.liouville n : ℝ)) (fun N : ℕ => (N : ℝ) ^ (1/2 + ε)) := by sorry

end BroughanRH
