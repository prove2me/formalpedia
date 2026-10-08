-- Prove2me | Theorems.Thm_BertsekasShreve_BorelInfinite_dp_converges
-- name    : BertsekasShreve.BorelInfinite.dp_converges
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T04:18:28.553029+00:00
-- url     : https://prove2.me/theorems/80f6c35a-e8c9-4805-bdee-96ac54f549f8
-- title:
--   Proposition 9.14 (SM part) — under (N) or (D) the DP algorithm converges to J*, uniformly under (D)
-- statement:
--   Let (SM) satisfy (N) or (D), and let $J_0 = 0$, $J_{k+1} = T(J_k)$ be the dynamic programming algorithm. Then
--
--   1. for every $x \in S$, $J_k(x)$ converges as $k \to \infty$, and its limit $J_\infty(x)$ satisfies
--   $$J_\infty = J^*; \tag{26}$$
--   2. under (D), for every lower semianalytic $J : S \to [-c, c]$ with $c < \infty$, the algorithm started at $J$ converges uniformly:
--   $$\lim_{k \to \infty} \sup_{x \in S} |T^k(J)(x) - J^*(x)| = 0. \tag{28}$$
--
--   Under (P) the limit $J_\infty$ can differ from $J^*$ (Example 1 of Chapter 9), which is why (P) is excluded.
--
--   **Formalization Note** Only the statements for (SM) are formalized. Eq. (26) is stated as convergence of $J_k(x)$ to $J^*(x)$ in $R^*$ for each $x$, which asserts both that the limit exists and that it equals $J^*(x)$. In Eq. (28) the absolute value is taken in $[0, \infty]$; under (D) both $T^k(J)$ and $J^*$ are real-valued and bounded, so it is the usual absolute difference.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 229, Definition 9.10; p. 231, Proposition 9.14, Eqs. (26), (28) (SM part)

import Mathlib
import Definitions.Def_BertsekasShreve_BorelInfinite_Analytic
import Definitions.Def_BertsekasShreve_BorelInfinite_ExtArith
import Definitions.Def_BertsekasShreve_BorelInfinite_Model
import Definitions.Def_BertsekasShreve_BorelInfinite_Policy

open MeasureTheory ProbabilityTheory Filter Topology

namespace BertsekasShreve.BorelInfinite

/-- **Proposition 9.14**, (SM) part (p. 231). (N)(D) The dynamic programming algorithm
`J₀ = 0`, `J_{k+1} = T(J_k)` (Definition 9.10) converges to the optimal cost:
`J_∞ = lim_k J_k = J*` (Eq. (26)). Under (D) it can be initiated from any lower semianalytic
`J : S → [−c, c]`, `c < ∞`, and converges uniformly:
`lim_{k→∞} sup_{x ∈ S} |T^k(J)(x) − J*(x)| = 0` (Eq. (28)). -/
theorem dp_converges {S C W : Type*}
    [TopologicalSpace S] [BertsekasShreve.AnalyticSelection.IsBorelSpace S] [MeasurableSpace S] [BorelSpace S] [Nonempty S]
    [TopologicalSpace C] [BertsekasShreve.AnalyticSelection.IsBorelSpace C] [MeasurableSpace C] [BorelSpace C] [Nonempty C]
    [TopologicalSpace W] [BertsekasShreve.AnalyticSelection.IsBorelSpace W] [MeasurableSpace W] [BorelSpace W] [Nonempty W]
    (M : Model S C W)
    (hcase : M.CaseN ∨ M.CaseD) :
    (∀ x, Tendsto (fun k => M.dpIter k x) atTop (𝓝 (M.Jstar x))) ∧
    (M.CaseD → ∀ (J : S → EReal) (c : ℝ), (∀ x, -(c : EReal) ≤ J x ∧ J x ≤ (c : EReal)) →
        IsLowerSemianalyticFun J →
        Tendsto (fun k => ⨆ x, ((M.T)^[k] J x - M.Jstar x).abs) atTop (𝓝 0)) := by sorry

end BertsekasShreve.BorelInfinite
