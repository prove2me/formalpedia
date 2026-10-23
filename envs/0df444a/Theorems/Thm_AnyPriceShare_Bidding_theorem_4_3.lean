-- Prove2me | Theorems.Thm_AnyPriceShare_Bidding_theorem_4_3
-- name    : AnyPriceShare.Bidding.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:15:01.406284+00:00
-- url     : https://prove2.me/theorems/015da7ef-f9ce-4385-8d3b-f7ea60ecb060
-- title:
--   Theorem 4.3, p. 14 — in the Bidding Game each agent can secure max{3/5·APS, TPS/(2−b_i), her ⌊1/b_i⌋ ranked item}
-- statement:
--   Consider $n$ agents with additive non-negative valuations $v_1,\dots,v_n$ over the items $M$ and entitlements $b_1,\dots,b_n$ ($b_k>0$, $\sum_kb_k=1$), playing the Bidding Game with their entitlements as budgets. Every agent $i$ has a strategy that, regardless of the strategies of the other agents, ensures she gets a bundle of value at least the largest of
--
--   1. $60\%$ of her AnyPrice share, $\frac35\,\mathrm{AnyPrice}(b_i,v_i,M)$;
--   2. $\frac1{2-b_i}$ of her Truncated Proportional Share, $\frac1{2-b_i}\,\mathrm{TPS}(b_i,v_i,M)$;
--   3. the value of her $\lfloor 1/b_i\rfloor$-ranked item.
--
--   $$\max\Big\{\tfrac35\,\mathrm{AnyPrice}(b_i,v_i,M),\ \tfrac1{2-b_i}\,\mathrm{TPS}(b_i,v_i,M),\ v_i\big(\text{item ranked }\lfloor 1/b_i\rfloor\big)\Big\}.$$
--
--   Running the game with every agent following such a strategy produces an allocation; with Proposition 4.2 this yields the main theorem (Theorem 1.3).
--
--   **Formalization Note** The paper's "allocation mechanism" is the Bidding Game itself, as encoded in the definitions. The sentence "Moreover, that mechanism runs in polynomial time" is not formalized. The ranked item is the $\lfloor1/b_i\rfloor$-th largest item value counted with multiplicity; since $b_i\le1$ the rank is at least $1$, and a rank above the number of items gives the value $0$.
-- source:
--   Babaioff, Ezra & Feige, Fair-Share Allocations for Agents with Arbitrary Entitlements, arXiv:2103.04304v4, p. 14, Theorem 4.3 (proof p. 17)

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_AnyPriceShare_Bidding_Game

namespace AnyPriceShare.Bidding

/-- Theorem 4.3, p. 14 (proof p. 17), without its polynomial-time sentence: in the Bidding Game
with additive valuations `v` and entitlements `b` (`b k > 0`, `∑ b k = 1`), every agent `i` has a
strategy that, regardless of the strategies of the other agents, guarantees her the largest of
`3/5 · AnyPrice(b_i, v_i, M)`, `1/(2 − b_i) · TPS(b_i, v_i, M)` and the value of her
`⌊1/b_i⌋`-ranked item. -/
theorem theorem_4_3 {n m : ℕ} (v : Fin n → Fin m → ℝ) (hv : ∀ i j, 0 ≤ v i j)
    (b : Fin n → ℝ) (hb : ∀ k, 0 < b k) (hsum : ∑ k, b k = 1) (i : Fin n) :
    ∃ σ : Strategy n m,
      Guarantees b σ i (v i)
        (max (max (3 / 5 * anyPrice (b i) (addVal (v i)) Finset.univ)
                  (1 / (2 - b i) * tps (b i) (v i) Finset.univ))
             (rankedValue (v i) Finset.univ ⌊1 / b i⌋₊)) := by sorry

end AnyPriceShare.Bidding
