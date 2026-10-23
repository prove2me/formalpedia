-- Prove2me | Theorems.Thm_AnyPriceShare_Bidding_lemma_D_3
-- name    : AnyPriceShare.Bidding.lemma_D_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:15:05.615991+00:00
-- url     : https://prove2.me/theorems/80a3b866-a8a8-4411-b38f-7d97250172c9
-- title:
--   Lemma D.3, p. 34 — the strategy of Lemma D.3 secures 1/(2−b_i) of the truncated proportional share
-- statement:
--   Consider the Bidding Game with budgets equal to the entitlements $b_1,\dots,b_n$ ($b_k>0$, $\sum_kb_k=1$), and an agent $i$ with additive non-negative item values $v(j)$. Every strategy of agent $i$ that follows the three rules of Lemma D.3 (bid the whole budget for one sufficient item; else half the budget for two items; else bid proportionally to the most valuable remaining item; drop out after a win under rule 1 or 2) guarantees her, regardless of the strategies of the other agents, a bundle of value at least
--
--   $$\frac{1}{2-b_i}\cdot\mathrm{TPS}(b_i,v,M).$$
--
--   By Proposition 4.2 this is also $\frac1{2-b_i}$ of the AnyPrice share, which is the $\frac1{2-b_i}$ part of the main theorem.
--
--   **Formalization Note** The rules are encoded as "rule 1, else rule 2, else rule 3"; since budgets are non-negative in every play, $b_i^{(t)}\le B^{(t)}$ and rule 2's first condition already excludes rule 1, so this is the paper's case split. The lemma covers every strategy satisfying the rules (every choice among equally valuable items). Legality of the prescribed bids (including the paper's remark that rule 3's bid is at most $b_i^{(t)}$) is part of the conclusion.
-- source:
--   Babaioff, Ezra & Feige, Fair-Share Allocations for Agents with Arbitrary Entitlements, arXiv:2103.04304v4, p. 34, Lemma D.3 (notation p. 33; proof pp. 34–36)

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_AnyPriceShare_Bidding_Game

namespace AnyPriceShare.Bidding

/-- Lemma D.3, p. 34: in the Bidding Game with entitlements `b` (`b k > 0`, `∑ b k = 1`), every
strategy of agent `i` following the three rules of Lemma D.3 guarantees her at least
`1/(2 − b_i) · TPS(b_i, v, M)`, regardless of the strategies of the other agents. -/
theorem lemma_D_3 {n m : ℕ} (v : Fin m → ℝ) (hv : ∀ j, 0 ≤ v j)
    (b : Fin n → ℝ) (hb : ∀ k, 0 < b k) (hsum : ∑ k, b k = 1) (i : Fin n)
    (σ : Strategy n m) (hσ : IsLemmaD3Strategy v b i σ) :
    Guarantees b σ i v (1 / (2 - b i) * tps (b i) v Finset.univ) := by sorry

end AnyPriceShare.Bidding
