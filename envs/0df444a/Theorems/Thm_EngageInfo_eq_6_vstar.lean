-- Prove2me | Theorems.Thm_EngageInfo_eq_6_vstar
-- name    : EngageInfo.eq_6_vstar
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:19:30.166006+00:00
-- url     : https://prove2.me/theorems/f024ef0f-d6fe-4065-8bbf-4b18c3c5d427
-- title:
--   (6) — the seller's equilibrium payoff $v^*(\alpha)$ in closed form
-- statement:
--   For every belief $\alpha\in[0,1]$, the seller's payoffs over all subgame-perfect equilibria of the subgame have a largest element, and
--
--   $$v^*(\alpha)=\begin{cases}\theta_L+\bar e-c, & \max\{\alpha_0,\alpha_1\}\le\alpha\le\alpha_{\bar e},\\ \max\{\theta_L-c,\ \alpha(\theta_H-c)\}, & \text{otherwise.}\end{cases}$$
--
--   This is the function whose concave closure gives the seller's optimal value. Under $\alpha_1<\alpha_{\bar e}$ it is non-monotonic, dropping at $\alpha_{\bar e}$, which is what makes partial information optimal.
--
--   Differences from the source:
--   - reading: "the seller's equilibrium expected payoff" v∗(α), with "the equilibrium" called unique (p.8) → v∗(α) = the maximum of the seller's payoffs over all pure subgame-perfect equilibria at belief α (seller-preferred equilibrium); reason: at α ∈ {α₀, α₁, α_ē} the subgame has several SPE with different seller payoffs; the closed interval of Lemma 1 and the values of (6) there are those of the seller-preferred SPE
--   - reading: the customer purchases in state ω (rule left implicit) → the customer buys iff θ_ω + e − p ≥ 0, i.e. also at indifference; reason: without purchase at indifference the seller has no best price and no SPE exists
--   - encoding: engagement e ∈ {0, ē}; SPE of the engagement–pricing subgame → engagement as Bool (true ↦ ē, false ↦ 0); pure-strategy SPE via the published CollabProject.TimeDep.SequentialGame.IsSPNE, the seller best-responding after each engagement level; reason: the §3 analysis is in pure strategies with the seller observing e; relabelling only
-- source:
--   Guo, Designing Information to Engage Customers, Management Science (2025), doi:10.1287/mnsc.2022.03503, §3.1, (6), p.10

import Mathlib
import Definitions.Def_EngageInfo_Params
import Definitions.Def_EngageInfo_vstar

namespace EngageInfo

/-- **The seller's equilibrium payoff (6).**
Guo, *Designing Information to Engage Customers*, Management Science (2025), §3.1, p.10, (6): "It
follows that the seller's equilibrium expected payoff is v∗(α) = θL + ē − c, if max{α₀, α₁} ≤ α ≤ αē;
max{θL − c, α(θH − c)}, if otherwise."

For every belief `α ∈ [0, 1]`, the set of the seller's subgame-perfect equilibrium payoffs has a
greatest element, equal to
`θ_L + ē − c` if `max{α₀, α₁} ≤ α ≤ α_ē`, and `max{θ_L − c, α(θ_H − c)}` otherwise;
hence `v*(α)` equals this value.

**Formalization Note** `v*` is defined as the supremum of the SPE payoffs (`vstar`), not by (6);
the `IsGreatest` clause shows the supremum is a maximum. No assumption `α₁ < α_ē` is needed (the
paper states (6) before adopting it). -/
theorem eq_6_vstar (M : Params) (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    IsGreatest (spePayoffs M α)
        (if M.m ≤ α ∧ α ≤ M.αbar then M.θL + M.ebar - M.c else max (M.θL - M.c) (α * (M.θH - M.c))) ∧
    vstar M α =
        (if M.m ≤ α ∧ α ≤ M.αbar then M.θL + M.ebar - M.c else max (M.θL - M.c) (α * (M.θH - M.c))) := by sorry

end EngageInfo
