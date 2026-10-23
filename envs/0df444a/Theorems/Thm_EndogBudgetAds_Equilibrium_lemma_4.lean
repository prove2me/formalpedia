-- Prove2me | Theorems.Thm_EndogBudgetAds_Equilibrium_lemma_4
-- name    : EndogBudgetAds.Equilibrium.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:34:27.977959+00:00
-- url     : https://prove2.me/theorems/05e7a1ea-2acf-4568-ae89-5dc734863659
-- title:
--   Lemma 4, p. 25 — on E_j(σ_j), bidder j's optimal budget multiplier is the largest
-- statement:
--   Fix a bidder $j$ and an admissible deviation $\sigma_j$, and let $B$ and $b$ be the budgets and bids of $(\sigma_j, \sigma^*_{-j})$ at a valuation profile $V \in E_j(\sigma_j)$. Then every optimal solution $(\bar\mu, \bar\nu)$ of the dual (10) of the ad network's LP satisfies
--   $$\bar\mu_j \ge \max_{k \ne j} \bar\mu_k.$$
--
--   Informally, on the event $E_j(\sigma_j)$ the deviating bidder's budget constraint is the most active one. This is the key step behind Lemma 3 and Lemma 6.
--
--   **Formalization Note** The paper writes "the optimal solution"; the statement is made for every optimal dual solution. It is pathwise, under the no-ties convention of p. 14 (no ties in $W$ or in $b$) and positive valuations, which hold almost surely.
-- source:
--   Ciocan & Iyer, SSRN 3240995, p. 25, Lemma 4 (dual (10), p. 25)

import Mathlib
import Definitions.Def_EndogBudgetAds_Equilibrium_Model
import Definitions.Def_EndogBudgetAds_Equilibrium_Proof
open MeasureTheory

namespace EndogBudgetAds.Equilibrium

/-- Lemma 4, p. 25 (pathwise, under the no-ties convention of p. 14 and positive valuations): on the
event `E_j(σ_j)`, every optimal solution `(μ̄, ν̄)` of the dual (10) of the ad network's LP under
`(σ_j, σ*_{−j})` has `μ̄_j ≥ max_{k ≠ j} μ̄_k`. -/
theorem lemma_4 (M : Market) (hM : M.Standing) (j : Fin M.m) (σj : Strategy M.n)
    (hσj : σj.Admissible) (V : Valuations M) (hVpos : ∀ l i, 0 < V l i)
    (hW : NoTies (W M V)) (hb : NoTies (bidsOf (deviate (sigmaStar M) j σj) V))
    (hV : V ∈ EventJ M j σj) (μ : Fin M.m → ℝ) (ν : Fin M.n → ℝ)
    (hopt : DualOptimal M (budgetsOf (deviate (sigmaStar M) j σj) V)
      (bidsOf (deviate (sigmaStar M) j σj) V) μ ν) :
    ∀ k, k ≠ j → μ k ≤ μ j := by sorry

end EndogBudgetAds.Equilibrium
