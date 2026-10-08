-- Prove2me | Theorems.Thm_BertsekasShreve_BorelInfinite_stationary_cost_fixed_point
-- name    : BertsekasShreve.BorelInfinite.stationary_cost_fixed_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T04:16:31.258349+00:00
-- url     : https://prove2.me/theorems/8d544a97-b613-43de-b5aa-94e1a0ec95f2
-- title:
--   Proposition 9.9 (SM part) — the cost of a stationary policy satisfies J_μ = T_μ(J_μ)
-- statement:
--   Let (SM) satisfy one of (P), (N) or (D), and let $\pi = (\mu, \mu, \dots)$ be a stationary policy, $\mu \in U(C \mid S)$. Then the cost $J_\mu$ of $\pi$ satisfies
--   $$J_\mu = T_\mu(J_\mu),$$
--   where $T_\mu(J)(x) = \int_C \big[ g(x, u) + \alpha \int_S J(x')\, t(dx' \mid x, u) \big] \mu(du \mid x)$.
--
--   This is the policy-evaluation equation of the model. It cannot be obtained from the optimality equation by restricting the controls to $\mu$, because the restricted constraint set need not be analytic.
--
--   **Formalization Note** Only the statement for the stochastic model (SM) is formalized; the statement for the deterministic model (DM) on $P(S)$ is not.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 226, Proposition 9.9 (SM part)

import Mathlib
import Definitions.Def_BertsekasShreve_BorelInfinite_Analytic
import Definitions.Def_BertsekasShreve_BorelInfinite_ExtArith
import Definitions.Def_BertsekasShreve_BorelInfinite_Model
import Definitions.Def_BertsekasShreve_BorelInfinite_Policy

open MeasureTheory ProbabilityTheory Filter Topology

namespace BertsekasShreve.BorelInfinite

/-- **Proposition 9.9**, (SM) part (p. 226). (P)(N)(D) If `π = (μ, μ, …)` is a stationary policy
for (SM), then `J_μ = T_μ(J_μ)`. -/
theorem stationary_cost_fixed_point {S C W : Type*}
    [TopologicalSpace S] [BertsekasShreve.AnalyticSelection.IsBorelSpace S] [MeasurableSpace S] [BorelSpace S] [Nonempty S]
    [TopologicalSpace C] [BertsekasShreve.AnalyticSelection.IsBorelSpace C] [MeasurableSpace C] [BorelSpace C] [Nonempty C]
    [TopologicalSpace W] [BertsekasShreve.AnalyticSelection.IsBorelSpace W] [MeasurableSpace W] [BorelSpace W] [Nonempty W]
    (M : Model S C W)
    (hcase : M.CaseP ∨ M.CaseN ∨ M.CaseD) (μ : M.UCS) :
    M.Jmu μ = M.Tmu μ (M.Jmu μ) := by sorry

end BertsekasShreve.BorelInfinite
