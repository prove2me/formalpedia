-- Prove2me | Theorems.Thm_AdWordsMSVV_Tradeoff_lemma_3
-- name    : AdWordsMSVV.Tradeoff.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:32:10.448538+00:00
-- url     : https://prove2.me/theorems/5f8c84d0-f3df-49b4-82cc-4c4e1c4d6e37
-- title:
--   Lemma 3, p. 8 — the value of the LPs L and D tends to N/e as k → ∞
-- statement:
--   Fix the number of bidders $N\ge0$. For each number of slabs $k$, let $\mathrm{val}(L_k)$ be the supremum of the objective of the factor-revealing LP $L$ over its feasible set and $\mathrm{val}(D_k)$ the infimum of the objective of its dual $D$. Then
--   $$\lim_{k\to\infty}\mathrm{val}(L_k)=\lim_{k\to\infty}\mathrm{val}(D_k)=\frac Ne .$$
--
--   For BALANCE this gives the competitive ratio $1-1/e$; for the tradeoff algorithm it supplies the $N/e$ term in the proof of Theorem 8.
--
--   **Formalization Note** The values are a real `sSup` and `sInf`. For $N\ge0$ the feasible sets are nonempty ($x=0$, $y=y^*$) and the objectives are bounded on them, so both are attained values; for $k\le1$ the index range is empty and both values are $0$, which does not affect the limit.
-- source:
--   Mehta, Saberi, Vazirani, Vazirani, AdWords and generalized on-line matching, J. ACM (2007), DOI 10.1145/1284320.1284321, p. 8, Lemma 3

import Mathlib
import Definitions.Def_AdWordsMSVV_Tradeoff_LP

namespace AdWordsMSVV.Tradeoff
theorem lemma_3 (N : ℕ) :
    Filter.Tendsto (fun k : ℕ => LValue k N) Filter.atTop (nhds ((N : ℝ) / Real.exp 1)) ∧
    Filter.Tendsto (fun k : ℕ => DValue k N) Filter.atTop (nhds ((N : ℝ) / Real.exp 1)) := by sorry
end AdWordsMSVV.Tradeoff
