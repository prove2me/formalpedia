-- Prove2me | Theorems.Thm_BroughanRH_liouvilleLimit
-- name    : BroughanRH.liouvilleLimit
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:13:04.961301+00:00
-- url     : https://prove2.me/theorems/633105a7-162f-4b2d-8028-54d18a1fe4e6
-- title:
--   Landau’s limit for Liouville sums
-- statement:
--   The Liouville sum through $N$, divided by $N^{1/2+\varepsilon}$, tends to zero for every $\varepsilon>0$.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, I Thm. 4.18. https://doi.org/10.1017/9781108178228

import Mathlib

namespace BroughanRH

theorem liouvilleLimit :
    ∀ ε : ℝ, 0 < ε → Filter.Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.liouville n : ℝ)) / (N : ℝ)^(1/2+ε)) Filter.atTop (nhds 0) := by sorry

end BroughanRH
