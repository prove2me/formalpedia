-- Prove2me | Theorems.Thm_AnyPriceShare_Bidding_lemma_4_7
-- name    : AnyPriceShare.Bidding.lemma_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:15:00.916768+00:00
-- url     : https://prove2.me/theorems/73984e37-facb-4990-acf3-0165e28a34cc
-- title:
--   Lemma 4.7, p. 19 — a strategy securing 3/2 · AnyPrice(b_i/2, v_i, M)
-- statement:
--   Consider the Bidding Game with budgets equal to the entitlements $b_1,\dots,b_n$ ($b_k>0$, $\sum_kb_k=1$), and an agent $i$ with additive non-negative item values $v(j)$. Agent $i$ has a strategy that guarantees her, regardless of the strategies of the other agents, a bundle of value at least
--
--   $$\frac32\cdot\mathrm{AnyPrice}\Big(\frac{b_i}{2},v,M\Big).$$
--
--   Note that $b_i/2$ is the entitlement inside the AnyPrice share, while the budgets in the game are still $b$. Lemma 4.7 is applied in step 3 of the strategy of Lemma 4.6, to a rescaled instance.
-- source:
--   Babaioff, Ezra & Feige, Fair-Share Allocations for Agents with Arbitrary Entitlements, arXiv:2103.04304v4, p. 19, Lemma 4.7 (restated and proved pp. 37–39)

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_AnyPriceShare_Bidding_Game

namespace AnyPriceShare.Bidding

/-- Lemma 4.7, p. 19 (proof pp. 37–39): in the Bidding Game with entitlements `b` (`b k > 0`,
`∑ b k = 1`), agent `i` has a strategy guaranteeing her at least `3/2 · AnyPrice(b_i/2, v, M)`,
regardless of the strategies of the other agents. -/
theorem lemma_4_7 {n m : ℕ} (v : Fin m → ℝ) (hv : ∀ j, 0 ≤ v j)
    (b : Fin n → ℝ) (hb : ∀ k, 0 < b k) (hsum : ∑ k, b k = 1) (i : Fin n) :
    ∃ σ : Strategy n m,
      Guarantees b σ i v (3 / 2 * anyPrice (b i / 2) (addVal v) Finset.univ) := by sorry

end AnyPriceShare.Bidding
