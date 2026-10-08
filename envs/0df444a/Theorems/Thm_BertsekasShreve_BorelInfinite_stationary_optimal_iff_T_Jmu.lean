-- Prove2me | Theorems.Thm_BertsekasShreve_BorelInfinite_stationary_optimal_iff_T_Jmu
-- name    : BertsekasShreve.BorelInfinite.stationary_optimal_iff_T_Jmu
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T04:18:10.65809+00:00
-- url     : https://prove2.me/theorems/ec8b828c-7a75-4bfc-b887-83b4661a52aa
-- title:
--   Proposition 9.13 (SM part) — under (N) or (D), (μ, μ, …) is optimal iff J_μ = T(J_μ)
-- statement:
--   Let (SM) satisfy (N) or (D), and let $\pi = (\mu, \mu, \dots)$ be a stationary policy, $\mu \in U(C \mid S)$. Then $\pi$ is optimal if and only if
--   $$J_\mu = T(J_\mu).$$
--
--   The test is applied to the cost of the candidate policy. The book states it for (N) and (D) only.
--
--   **Formalization Note** Only the statement for (SM) is formalized.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 228, Proposition 9.13 (SM part)

import Mathlib
import Definitions.Def_BertsekasShreve_BorelInfinite_Analytic
import Definitions.Def_BertsekasShreve_BorelInfinite_ExtArith
import Definitions.Def_BertsekasShreve_BorelInfinite_Model
import Definitions.Def_BertsekasShreve_BorelInfinite_Policy

open MeasureTheory ProbabilityTheory Filter Topology

namespace BertsekasShreve.BorelInfinite

/-- **Proposition 9.13**, (SM) part (p. 228). (N)(D) Let `π = (μ, μ, …)` be a stationary policy in
(SM). The policy `π` is optimal if and only if `J_μ = T(J_μ)`. -/
theorem stationary_optimal_iff_T_Jmu {S C W : Type*}
    [TopologicalSpace S] [BertsekasShreve.AnalyticSelection.IsBorelSpace S] [MeasurableSpace S] [BorelSpace S] [Nonempty S]
    [TopologicalSpace C] [BertsekasShreve.AnalyticSelection.IsBorelSpace C] [MeasurableSpace C] [BorelSpace C] [Nonempty C]
    [TopologicalSpace W] [BertsekasShreve.AnalyticSelection.IsBorelSpace W] [MeasurableSpace W] [BorelSpace W] [Nonempty W]
    (M : Model S C W)
    (hcase : M.CaseN ∨ M.CaseD) (μ : M.UCS) :
    M.IsOptimal μ.toPolicy ↔ M.Jmu μ = M.T (M.Jmu μ) := by sorry

end BertsekasShreve.BorelInfinite
