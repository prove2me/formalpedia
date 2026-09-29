-- Prove2me | Theorems.Thm_BinPacking_FirstFit_ratio_limit_eq
-- name    : BinPacking.FirstFit.ratio_limit_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T22:09:19.234984+00:00
-- url     : https://prove2.me/theorems/740b072f-5904-4c56-99df-302b8f5c2354
-- title:
--   Corollary of Section 2 — $\lim_{k\to\infty}R_{FF}(k)=\lim_{k\to\infty}R_{BF}(k)=1.7$
-- statement:
--   For $k\ge 1$ let $R_{FF}(k)$ (respectively $R_{BF}(k)$) be the largest value of the ratio $FF(L)/L^*$ (respectively $BF(L)/L^*$) over all lists $L$ of reals in $(0,1]$ with $L^*=k$. Then
--
--   $$\lim_{k\to\infty}R_{FF}(k)=1.7\qquad\text{and}\qquad\lim_{k\to\infty}R_{BF}(k)=1.7.$$
--
--   This is the asymptotic worst-case performance ratio of First-Fit and Best-Fit: on lists with large optimum, neither algorithm ever uses more than about $70\%$ more bins than necessary, and for both there are lists on which it does use about $70\%$ more.
--
--   **Formalization Note** $R_{FF}(k)$ and $R_{BF}(k)$ are suprema in the extended nonnegative reals $[0,\infty]$ and the limit is taken there, so the statement asserts both that the ratios are eventually at most $1.7+\varepsilon$ and that they eventually exceed $1.7-\varepsilon$.
-- source:
--   Johnson, Demers, Ullman, Garey, Graham, Worst-Case Performance Bounds for Simple One-Dimensional Packing Algorithms, SIAM J. Comput. 3(4) (1974), p. 306, Corollary of Section 2 (after Theorem 2.2)

import Mathlib
import Definitions.Def_BinPacking_FirstFit_Model

namespace BinPacking.FirstFit

/-- Corollary of Section 2 (p. 306): (i) `lim_{k→∞} R_FF(k) = 1.7` and
(ii) `lim_{k→∞} R_BF(k) = 1.7`, where `R_FF(k)`, `R_BF(k)` are the suprema of `FF(L)/L*`,
`BF(L)/L*` over all lists with `L* = k`, taken in `ℝ≥0∞`. -/
theorem ratio_limit_eq :
    Filter.Tendsto ratioFF Filter.atTop (nhds ((17 : ENNReal) / 10)) ∧
    Filter.Tendsto ratioBF Filter.atTop (nhds ((17 : ENNReal) / 10)) := by sorry

end BinPacking.FirstFit
