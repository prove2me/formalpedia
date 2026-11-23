-- Prove2me | Theorems.Thm_ForwardRM_Cutoffs_Supplement_posted_prices_near_optimal
-- name    : ForwardRM.Cutoffs.Supplement.posted_prices_near_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T20:24:14.454169+00:00
-- url     : https://prove2.me/theorems/a2c04a10-3177-465a-b322-e537a4f8feb4
-- title:
--   Theorem 3 — posted prices with a final second-price auction obtain Π* − O(h)
-- statement:
--   Consider the continuous-time model with $K$ units, discount rate $r>0$ and a Poisson entry rate $\lambda$ that is Lipschitz continuous on $[0,T]$. Let $\Pi^*(h)$ be the optimal profit of the discretized problem with period length $h=T/n$. Then:
--
--   1. the continuous-time profit $\Pi^*=\lim_{h\to0}\Pi^*(h)$ exists, taken along $h=T/n$;
--   2. posted prices with a second-price auction for the last unit at time $T$ obtain $\Pi^*-O(h)$. There are constants $A>0$ and $h_0>0$ such that for every $h=T/n<h_0$ some posted-price policy, with the final auction at reserve $e^{-rT}m^{-1}(0)$, has an equilibrium $\sigma$ of the buyers' game with
--
--   $$\mathbb E_\sigma\Big[\sum\text{payments}\Big]\ \ge\ \Pi^*-A\,h .$$
--
--   The result says that, as periods become short, the optimal mechanism of §4 can be implemented by posted prices together with one final auction. The seller does not need to elicit the values of the lower buyers, run repeated auctions, or condition prices on arrivals. Lemma 7 (p. 38) restates the theorem word for word.
--
--   **Formalization Note** No positive lower slope of marginal revenue is assumed in this theorem: the printed theorem has none, and the failure of the proof’s cutoff lemmas does not refute this implementation statement. Its proof remains a draft obligation. The posted-price game, its equilibrium and the seller's revenue are those of the definition `PostedPrice`. Prices depend only on the period and the public history of sale counts. The equilibrium allows every alternative strategy adapted to the public history. Revenue is the expected sum of payments. $A$ and $h_0$ may depend on the primitives and on $K$.
--
--   Differences from the source:
--   - reading: Π* = lim_{h→0} Π*(h), "defined" on p. 19 → existence of the limit along h = T/n is part of the conclusion; reason: the discretization ends with a sale at T (p. 19, "last unit at time T"), so h = T/n, and the proof supplies Π* − Π*(h) ≤ rhΠ* (p. 40)
--   - reading: "she can obtain Π* − O(h)" → ∃ A > 0, h₀ > 0 such that for every h = T/n < h₀ some posted-price policy and an equilibrium of it give expected payments ≥ Π* − Ah; reason: the bound is one-sided, as "can obtain" says, and O(h) refers to h → 0 with constants from the proof
--   - reading: "a second-price auction for the last unit" → reserve e^{−rT}m^{−1}(0); reason: this is the mechanism of the proof (p. 38); fixing the reserve leaves fewer mechanisms to choose from, so the statement implies the printed one
--   - reading: "posted prices" with buyers who best respond → symmetric pure strategies of (value, entry period, public history of sale counts), measurable in the value with bounded bids, from which no type gains by any alternative strategy adapted to the public history; reason: the public information of §5 (p. 19) is the price path and the inventory, both functions of past sales; the buyer's problem is (A.9), and Poisson entry makes the tagged buyer's view of the others independent of his entry (p. 39)
--   - encoding: payments and bids in time-0 units, the utility of a buyer served at t = ih is e^{−rt}v − p, and Π*(h) = e^{−rh}Π̃^K_1(∅) → these conventions in Lean; reason: (A.9) and the reserve e^{−rT}m^{−1}(0) use time-0 units, and the extra e^{−rh} → 1 does not change Π*; a bid below the reserve stands for "no bid", which has the same outcome
-- source:
--   Board, Skrzypacz, Revenue Management with Forward-Looking Buyers, J. Political Economy 124(4) (2016), accepted manuscript of Feb. 6, 2015, p. 20, Theorem 3 (restated as Lemma 7, p. 38; proof pp. 36–40, Appendix A.3)

import Mathlib
import Definitions.Def_ForwardRM_Cutoffs_Model
import Definitions.Def_ForwardRM_Cutoffs_ValueFunction
import Definitions.Def_ForwardRM_Cutoffs_Supplement_ContinuousModel
import Definitions.Def_ForwardRM_Cutoffs_Supplement_PostedPrice

namespace ForwardRM.Cutoffs.Supplement

/-- Theorem 3 (Board–Skrzypacz, p. 20; restated as Lemma 7, p. 38). Suppose the arrival rate is
Lipschitz on `[0, T]`. Then, with `K` units:

1. the continuous-time profit `Π* = lim_{h → 0} Π*(h)` exists, along the grids `h = T/n`;
2. posted prices with a second-price auction (reserve `e^{−rT} m⁻¹(0)`) for the last unit at time
   `T` obtain `Π* − O(h)`: there are `A > 0` and `h₀ > 0` such that for every `h = T/n < h₀` some
   posted-price policy has an equilibrium of the buyers' game whose expected payments to the seller
   are at least `Π* − A h`. -/
theorem posted_prices_near_optimal (C : ContinuousModel) (K : ℕ) (hlip : C.LipschitzRate) :
    ∃ Pstar : ℝ,
      Filter.Tendsto (fun n : ℕ => C.optProfit K (n + 1) (Nat.le_add_left 1 n)) Filter.atTop
        (nhds Pstar) ∧
      ∃ A : ℝ, 0 < A ∧ ∃ h₀ : ℝ, 0 < h₀ ∧
        ∀ (n : ℕ) (hn : 1 ≤ n), C.step n < h₀ →
          ∃ (p : PostedPricePolicy) (σ : BuyerStrategy),
            C.IsEquilibrium n hn p σ K ∧ Pstar - A * C.step n ≤ C.sellerRevenue n hn p σ K := by sorry

end ForwardRM.Cutoffs.Supplement
