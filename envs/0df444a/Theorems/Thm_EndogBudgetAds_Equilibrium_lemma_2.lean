-- Prove2me | Theorems.Thm_EndogBudgetAds_Equilibrium_lemma_2
-- name    : EndogBudgetAds.Equilibrium.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:34:35.126472+00:00
-- url     : https://prove2.me/theorems/573963ac-9b10-4f44-a32f-870cd54973db
-- title:
--   Lemma 2, p. 23 — k's spend on the items she tops is at most Ψ̄_k + Ξ_k(σ_j)
-- statement:
--   Fix bidders $j \ne k$ and a deviation $\sigma_j$ of bidder $j$, and let $b$ be the bid vector of $(\sigma_j, \sigma^*_{-j})$ at a valuation profile $V$. If bidder $k$ were allocated every item on which she has the highest bid, her payments would be bounded by her unbudgeted equilibrium spend plus the slack term:
--   $$\sum_{i \in [n]} p^b(i,k)\,\mathbf 1\{i \in U^b_{k,1}\} \le \bar\Psi_k + \Xi_k(\sigma_j).$$
--
--   This deterministic inequality explains why the budget $B^*_k$ guards bidder $k$ against both overbidding and underbidding by $j$: on the event $E_j(\sigma_j)$, the right-hand side is below $B^*_k$.
--
--   **Formalization Note** The statement is pathwise, under the paper's no-ties convention (p. 14), here the hypotheses that neither $W$ nor $b$ has ties on any item, and positive valuations $V_{ij} > 0$; both hold almost surely under the exponential law.
-- source:
--   Ciocan & Iyer, SSRN 3240995, p. 23, Lemma 2

import Mathlib
import Definitions.Def_EndogBudgetAds_Equilibrium_Model
import Definitions.Def_EndogBudgetAds_Equilibrium_Proof
open MeasureTheory

namespace EndogBudgetAds.Equilibrium

/-- Lemma 2, p. 23 (pathwise, under the paper's no-ties convention of p. 14 and positive valuations):
bidder `k ≠ j`'s payments on the items she tops under `(σ_j, σ*_{−j})` are at most `Ψ̄_k + Ξ_k(σ_j)`. -/
theorem lemma_2 (M : Market) (hM : M.Standing) (j k : Fin M.m) (hkj : k ≠ j)
    (σj : Strategy M.n) (V : Valuations M) (hVpos : ∀ l i, 0 < V l i)
    (hW : NoTies (W M V)) (hb : NoTies (bidsOf (deviate (sigmaStar M) j σj) V)) :
    (∑ i, if IsTop (fun l => bidsOf (deviate (sigmaStar M) j σj) V l i) k then
        pay (bidsOf (deviate (sigmaStar M) j σj) V) i k else 0) ≤
      PsiBar M k V + Xi M j k σj V := by sorry

end EndogBudgetAds.Equilibrium
