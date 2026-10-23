-- Prove2me | Theorems.Thm_AnyPriceShare_Bidding_lemma_4_6
-- name    : AnyPriceShare.Bidding.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:15:10.13698+00:00
-- url     : https://prove2.me/theorems/1ada9bff-2dbe-4211-86f3-f9c1f6dfd320
-- title:
--   Lemma 4.6, p. 18 — a strategy securing 60% of the AnyPrice share
-- statement:
--   Consider the Bidding Game with budgets equal to the entitlements $b_1,\dots,b_n$ ($b_k>0$, $\sum_kb_k=1$), and an agent $i$ with additive non-negative item values $v(j)$. Agent $i$ has a strategy that guarantees her, regardless of the strategies of the other agents, a bundle of value at least
--
--   $$\frac35\cdot\mathrm{AnyPrice}(b_i,v,M),$$
--
--   that is, $60\%$ of her AnyPrice share. This is the $3/5$ part of the main theorem.
-- source:
--   Babaioff, Ezra & Feige, Fair-Share Allocations for Agents with Arbitrary Entitlements, arXiv:2103.04304v4, p. 18, Lemma 4.6 (proof pp. 18–19)

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_AnyPriceShare_Bidding_Game

namespace AnyPriceShare.Bidding

/-- Lemma 4.6, p. 18 (proof pp. 18–19): in the Bidding Game with entitlements `b` (`b k > 0`,
`∑ b k = 1`), agent `i` has a strategy guaranteeing her at least `60%` of `AnyPrice(b_i, v, M)`,
regardless of the strategies of the other agents. -/
theorem lemma_4_6 {n m : ℕ} (v : Fin m → ℝ) (hv : ∀ j, 0 ≤ v j)
    (b : Fin n → ℝ) (hb : ∀ k, 0 < b k) (hsum : ∑ k, b k = 1) (i : Fin n) :
    ∃ σ : Strategy n m,
      Guarantees b σ i v (3 / 5 * anyPrice (b i) (addVal v) Finset.univ) := by sorry

end AnyPriceShare.Bidding
