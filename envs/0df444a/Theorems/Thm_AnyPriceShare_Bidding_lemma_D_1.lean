-- Prove2me | Theorems.Thm_AnyPriceShare_Bidding_lemma_D_1
-- name    : AnyPriceShare.Bidding.lemma_D_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:24.1756+00:00
-- url     : https://prove2.me/theorems/7e3e6d11-e1db-4fde-9774-a2f0f5ee8568
-- title:
--   Lemma D.1, p. 33 — TPS(b_i, v_i, M) ≤ TPS(b_i/(1−|K|·b_i), v_i, M∖K) for K ⊂ M and b_i ≤ 1/(|K|+1)
-- statement:
--   Let an agent have an additive valuation with non-negative item values $u(j)$ on a set of items $S$, let $K\subsetneq S$ be a proper subset of the items, and let the entitlement satisfy $0<\beta\le\frac1{|K|+1}$. Then removing the items of $K$ and rescaling the entitlement does not decrease the Truncated Proportional Share:
--
--   $$\mathrm{TPS}(\beta,u,S)\ \le\ \mathrm{TPS}\Big(\frac{\beta}{1-|K|\cdot\beta},\,u,\,S\setminus K\Big).$$
--
--   In the Bidding Game this is what makes a round lost by agent $i$ harmless for a TPS guarantee: the remaining instance, with budgets rescaled to sum to $1$, has at least the same TPS. It is used in the proof of Lemma D.3.
--
--   **Formalization Note** The item set is a general finite set $S$ (the paper's $\mathcal M$), so the lemma can be applied to the remaining items of a play. $K\subset S$ is kept strict, as printed. $\beta>0$ is the model's $b_i>0$; the bound $\beta\le1/(|K|+1)$ makes $1-|K|\beta\ge\beta>0$.
-- source:
--   Babaioff, Ezra & Feige, Fair-Share Allocations for Agents with Arbitrary Entitlements, arXiv:2103.04304v4, p. 33, Lemma D.1

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic

namespace AnyPriceShare.Bidding

/-- Lemma D.1, p. 33: for a set of items `K ⊂ S`, an entitlement `0 < β ≤ 1/(|K|+1)` and an
additive valuation with non-negative item values `u`,
`TPS(β, u, S) ≤ TPS(β / (1 − |K| · β), u, S ∖ K)`. -/
theorem lemma_D_1 {m : ℕ} (u : Fin m → ℝ) (hu : ∀ j, 0 ≤ u j)
    (S K : Finset (Fin m)) (hK : K ⊂ S)
    (β : ℝ) (hβ : 0 < β) (hβK : β ≤ 1 / ((K.card : ℝ) + 1)) :
    tps β u S ≤ tps (β / (1 - (K.card : ℝ) * β)) u (S \ K) := by sorry

end AnyPriceShare.Bidding
