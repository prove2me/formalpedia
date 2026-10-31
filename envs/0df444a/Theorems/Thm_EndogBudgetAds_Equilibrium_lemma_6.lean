-- Prove2me | Theorems.Thm_EndogBudgetAds_Equilibrium_lemma_6
-- name    : EndogBudgetAds.Equilibrium.lemma_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:34:39.231652+00:00
-- url     : https://prove2.me/theorems/1dddb255-e764-4246-a896-03c19222b851
-- title:
--   Lemma 6, p. 30 — on E_j(σ*_j), every optimal allocation under σ* is greedy
-- statement:
--   Suppose every bidder plays $\sigma^*$, with bids $b = W$ and budgets $B^*$, and fix a bidder $j$. On the event $E_j(\sigma^*_j)$, every optimal solution $Y$ of the ad network's LP (2) is greedy:
--   $$Y_{ik} = \mathbf 1\{i \in U^W_{k,1},\ W^{(2)}_i \ge \delta\} \quad \text{for all } i, k.$$
--
--   So on this event the network simply runs a second-price auction on each item with reserve $\delta$; this is what makes the equilibrium allocation tractable.
--
--   **Formalization Note** Pathwise, under the no-ties convention of p. 14 (no ties in $W$), $W^{(2)}_i \ne \delta$ for every item, and positive valuations; all hold almost surely. Stating the conclusion for every optimal $Y$ also gives the uniqueness the proof mentions.
-- source:
--   Ciocan & Iyer, SSRN 3240995, p. 30, Lemma 6 (Definition 1, p. 14)

import Mathlib
import Definitions.Def_EndogBudgetAds_Equilibrium_Model
import Definitions.Def_EndogBudgetAds_Equilibrium_Proof
open MeasureTheory

namespace EndogBudgetAds.Equilibrium

/-- Lemma 6, p. 30 (pathwise, under the no-ties convention of p. 14, `W_i^{(2)} ≠ δ` and positive
valuations): when every bidder plays σ*, on the event `E_j(σ*_j)` every optimal allocation of the LP (2)
is greedy. -/
theorem lemma_6 (M : Market) (hM : M.Standing) (j : Fin M.m) (V : Valuations M)
    (hVpos : ∀ l i, 0 < V l i) (hW : NoTies (W M V))
    (hδ : ∀ i, top2 (fun l => W M V l i) ≠ M.δ)
    (hV : V ∈ EventJ M j (sigmaStar M j)) :
    ∀ Y, AllocOptimal M (budgetsOf (sigmaStar M) V) (bidsOf (sigmaStar M) V) Y →
      IsGreedy M (bidsOf (sigmaStar M) V) Y := by sorry

end EndogBudgetAds.Equilibrium
