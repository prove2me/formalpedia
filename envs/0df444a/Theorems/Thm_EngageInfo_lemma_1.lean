-- Prove2me | Theorems.Thm_EngageInfo_lemma_1
-- name    : EngageInfo.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:19:42.253682+00:00
-- url     : https://prove2.me/theorems/37c9458f-10cb-48b2-844d-bbd04cd33e82
-- title:
--   Lemma 1 — the customer engages in equilibrium exactly when $\max\{\alpha_0,\alpha_1\}\le\alpha\le\alpha_{\bar e}$
-- statement:
--   For every belief $\alpha\in[0,1]$:
--
--   1. the subgame has a pure subgame-perfect equilibrium;
--   2. if $\max\{\alpha_0,\alpha_1\}\le\alpha\le\alpha_{\bar e}$, some equilibrium has the customer engaged ($e^*=\bar e$), and every equilibrium that gives the seller its equilibrium payoff $v^*(\alpha)$ has the customer engaged;
--   3. otherwise, every equilibrium has the customer not engaged ($e^*=0$).
--
--   Here $\alpha_1=k/\Theta$. The customer engages only at intermediate beliefs, because only there does the seller's price respond to engagement by less than $\bar e$.
--
--   Differences from the source:
--   - reading: "the customer chooses to be engaged in equilibrium (i.e., e∗ = ē) when and only when" max{α₀, α₁} ≤ α ≤ αē → on the interval some SPE engages and every SPE with seller payoff v∗(α) engages; off it every SPE has e = 0; and an SPE exists; reason: "the equilibrium" presupposes existence; at the endpoints α₀, α₁, α_ē there are also SPE without engagement, and the closed interval is the seller-preferred equilibrium of (6)
--   - reading: "the seller's equilibrium expected payoff" v∗(α), with "the equilibrium" called unique (p.8) → v∗(α) = the maximum of the seller's payoffs over all pure subgame-perfect equilibria at belief α (seller-preferred equilibrium); reason: at α ∈ {α₀, α₁, α_ē} the subgame has several SPE with different seller payoffs; the closed interval of Lemma 1 and the values of (6) there are those of the seller-preferred SPE
--   - reading: the customer purchases in state ω (rule left implicit) → the customer buys iff θ_ω + e − p ≥ 0, i.e. also at indifference; reason: without purchase at indifference the seller has no best price and no SPE exists
--   - encoding: engagement e ∈ {0, ē}; SPE of the engagement–pricing subgame → engagement as Bool (true ↦ ē, false ↦ 0); pure-strategy SPE via the published CollabProject.TimeDep.SequentialGame.IsSPNE, the seller best-responding after each engagement level; reason: the §3 analysis is in pure strategies with the seller observing e; relabelling only
-- source:
--   Guo, Designing Information to Engage Customers, Management Science (2025), doi:10.1287/mnsc.2022.03503, Lemma 1, p.10

import Mathlib
import Definitions.Def_CollabProject_TimeDep_Game
import Definitions.Def_EngageInfo_Params
import Definitions.Def_EngageInfo_subgame
import Definitions.Def_EngageInfo_vstar

namespace EngageInfo

open CollabProject.TimeDep

/-- **Lemma 1: the customer engages exactly at intermediate beliefs.**
Guo, *Designing Information to Engage Customers*, Management Science (2025), Lemma 1, p.10: "Under
observable customer engagement, the customer chooses to be engaged in equilibrium (i.e., e∗ = ē)
when and only when the belief on the basic value is intermediate, i.e., max{α₀, α₁} ≤ α ≤ αē, where
α₁ ≡ k/Θ."

For every belief `α ∈ [0, 1]`:
1. the subgame has a (pure) subgame-perfect equilibrium;
2. if `max{α₀, α₁} ≤ α ≤ α_ē`, some SPE has the customer engaged, and every SPE that gives the
   seller its equilibrium payoff `v*(α)` has the customer engaged;
3. otherwise every SPE has the customer not engaged.

**Formalization Note** `v*(α)` is the seller-preferred SPE payoff (`vstar`). At the endpoints
`α ∈ {α₀, α₁, α_ē}` of the interval the subgame also has SPE without engagement, with a lower seller
payoff; clause 2 reads the paper's "in equilibrium" as the seller-preferred equilibrium. The lemma
does not use the assumption `α₁ < α_ē` of p.10, and the statement does not assume it. -/
theorem lemma_1 (M : Params) (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    (∃ (b : Bool) (P : Bool → ℝ), (subgame M α).IsSPNE b P) ∧
    (M.m ≤ α ∧ α ≤ M.αbar →
      (∃ P : Bool → ℝ, (subgame M α).IsSPNE true P) ∧
      ∀ (b : Bool) (P : Bool → ℝ), (subgame M α).IsSPNE b P →
        sellerProfit M α (effort M b) (P b) = vstar M α → b = true) ∧
    (¬ (M.m ≤ α ∧ α ≤ M.αbar) →
      ∀ (b : Bool) (P : Bool → ℝ), (subgame M α).IsSPNE b P → b = false) := by sorry

end EngageInfo
