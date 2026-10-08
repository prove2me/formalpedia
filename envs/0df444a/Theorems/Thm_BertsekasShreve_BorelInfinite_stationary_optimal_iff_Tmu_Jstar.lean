-- Prove2me | Theorems.Thm_BertsekasShreve_BorelInfinite_stationary_optimal_iff_Tmu_Jstar
-- name    : BertsekasShreve.BorelInfinite.stationary_optimal_iff_Tmu_Jstar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T04:17:53.807584+00:00
-- url     : https://prove2.me/theorems/050c55f3-da74-4322-80b8-2bf9a311fad0
-- title:
--   Proposition 9.12 (SM part) — under (P) or (D), (μ, μ, …) is optimal iff J* = T_μ(J*)
-- statement:
--   Let (SM) satisfy (P) or (D), and let $\pi = (\mu, \mu, \dots)$ be a stationary policy, $\mu \in U(C \mid S)$. Then $\pi$ is optimal, i.e. $J_\mu(x) = J^*(x)$ for every $x \in S$, if and only if
--   $$J^* = T_\mu(J^*).$$
--
--   This is the condition used to build an optimal stationary policy from a minimizer of the right side of the optimality equation (Corollary 9.12.1). The book states it for (P) and (D) only.
--
--   **Formalization Note** Only the statement for (SM) is formalized.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 227, Proposition 9.12 (SM part)

import Mathlib
import Definitions.Def_BertsekasShreve_BorelInfinite_Analytic
import Definitions.Def_BertsekasShreve_BorelInfinite_ExtArith
import Definitions.Def_BertsekasShreve_BorelInfinite_Model
import Definitions.Def_BertsekasShreve_BorelInfinite_Policy

open MeasureTheory ProbabilityTheory Filter Topology

namespace BertsekasShreve.BorelInfinite

/-- **Proposition 9.12**, (SM) part (p. 227). (P)(D) Let `π = (μ, μ, …)` be a stationary policy in
(SM). The policy `π` is optimal if and only if `J* = T_μ(J*)`. -/
theorem stationary_optimal_iff_Tmu_Jstar {S C W : Type*}
    [TopologicalSpace S] [BertsekasShreve.AnalyticSelection.IsBorelSpace S] [MeasurableSpace S] [BorelSpace S] [Nonempty S]
    [TopologicalSpace C] [BertsekasShreve.AnalyticSelection.IsBorelSpace C] [MeasurableSpace C] [BorelSpace C] [Nonempty C]
    [TopologicalSpace W] [BertsekasShreve.AnalyticSelection.IsBorelSpace W] [MeasurableSpace W] [BorelSpace W] [Nonempty W]
    (M : Model S C W)
    (hcase : M.CaseP ∨ M.CaseD) (μ : M.UCS) :
    M.IsOptimal μ.toPolicy ↔ M.Jstar = M.Tmu μ M.Jstar := by sorry

end BertsekasShreve.BorelInfinite
