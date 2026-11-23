-- Prove2me | Theorems.Thm_ArapostathisAC_VanishingDiscount_Supplement_theorem_4_4
-- name    : ArapostathisAC.VanishingDiscount.Supplement.theorem_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:06:03.194481+00:00
-- url     : https://prove2.me/theorems/2f29dd04-a1a6-4f71-a79a-d4ddc52384db
-- title:
--   Theorem 4.4 — on a finite state space with compact actions, under Assumptions 2.1–2.3 an $\varepsilon$-optimal $f\in\Pi_{SD}$ exists for every $\varepsilon>0$
-- statement:
--   Let the state space $S$ be finite (discrete topology) and the action space $A$ a compact metric space, with nonempty compact admissible sets $U(i)$ (§4.2). Under Assumptions 2.1–2.3, for every $\varepsilon>0$ there is $f\in\Pi_{SD}$ that is $\varepsilon$-optimal for the average cost criterion:
--   $$J(\mu,f)\le J^*(\mu)+\varepsilon\qquad\text{for every initial distribution }\mu\in\mathcal P(S),$$
--   where $J^*(\mu)=\inf_{\pi\in\Pi}J(\mu,\pi)$ is taken over all admissible (history-dependent, randomized) policies.
--
--   With infinitely many actions an average optimal stationary deterministic policy need not exist; this theorem shows that stationary deterministic policies still come arbitrarily close.
--
--   **Formalization Note** $J$ and $J^*$ take values in $[0,\infty]$. The finite discrete state space is given the standard Borel structure required by the published model.
--
--   Differences from the source:
--   - encoding: J(μ, π) and J*(μ) as real or extended-real numbers → values in [0, ∞] (lintegrals of the nonnegative cost), compared in EReal where signed terms occur; reason: Lean convention; costs are nonnegative on K (Assumption 2.1), so the instances are the same and infinite values are represented exactly
--   - encoding: S = {1, …, k} with the discrete topology → a finite type with discrete topology, Borel and standard Borel σ-algebra; reason: Lean convention; the same spaces
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 298, Theorem 4.4; p. 293, §4.2 setting; p. 288, Assumptions 2.1–2.3

import Mathlib
import Definitions.Def_ArapostathisAC_CanonicalTriplet_CMP
import Definitions.Def_ArapostathisAC_VanishingDiscount_Supplement_BorelCriteria

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open ArapostathisAC.CanonicalTriplet

namespace ArapostathisAC.VanishingDiscount.Supplement

/-- Theorem 4.4 (p. 298). Finite state space `S` (discrete topology), compact metric action space
`A` with nonempty compact admissible sets `U(i)`. Under Assumptions 2.1–2.3, for every `ε > 0`
there is an `ε`-optimal `f ∈ Π_SD`: `J(μ, f) ≤ J*(μ) + ε` for every initial distribution `μ`,
where `J*(μ)` is the infimum over all admissible policies. -/
theorem theorem_4_4 {S A : Type*} [Fintype S] [TopologicalSpace S] [DiscreteTopology S]
    [MeasurableSpace S] [BorelSpace S] [StandardBorelSpace S]
    [MetricSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : BorelCMP S A) (h22 : Assumption22 M) (h23 : Assumption23 M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f : StationaryPolicy M, IsAvgEpsOptimal M ε f.toPolicy := by sorry

end ArapostathisAC.VanishingDiscount.Supplement
