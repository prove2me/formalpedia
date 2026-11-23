-- Prove2me | Theorems.Thm_ArapostathisAC_VanishingDiscount_Supplement_theorem_4_5
-- name    : ArapostathisAC.VanishingDiscount.Supplement.theorem_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:07:04.167838+00:00
-- url     : https://prove2.me/theorems/346d5055-c91f-40be-824c-2cc528525e99
-- title:
--   Theorem 4.5 — on a finite state space with compact actions, Assumptions 2.1–2.2, continuity of $c(\cdot)$ on $\Pi_{SR}$ and unichain chains under every $f\in\Pi_{SR}$ give an optimal $f\in\Pi_{SD}$
-- statement:
--   Let $S$ be finite and $A$ a compact metric space (§4.2). Assume Assumptions 2.1 and 2.2, that the cost vector
--   $$f\mapsto c(f)=\Big(\int_Ac(i,a)\,f(i)(da)\Big)_{i\in S}$$
--   is continuous on $\Pi_{SR}$ (randomized decision rules with $f(i)(U(i))=1$, with the product of the weak topologies), and that under every $f\in\Pi_{SR}$ the chain with transition matrix $P(f)(i,j)=\int P(j\mid i,a)f(i)(da)$ is unichain. Then there is an optimal $f\in\Pi_{SD}$: $J(\mu,f)\le J^*(\mu)+\varepsilon$ for every $\varepsilon>0$ and every initial distribution $\mu$.
--
--   Under the unichain assumption $P^*(\cdot)$ and hence $J(\cdot)$ are continuous on the compact set $\Pi_{SR}$, which is why an optimum is attained.
--
--   **Formalization Note** $c(f)$ takes values in $[0,\infty]^S$; continuity is with respect to the product topology on $\prod_{i\in S}\mathcal P(A)$, each factor with the topology of weak convergence.
--
--   Differences from the source:
--   - reading: c(·) is continuous on Π_SR → f ↦ (∫ c(i, a) f(i)(da))_i is continuous from the admissible rules in ∏_i 𝒫(A) (product of weak topologies) to [0, ∞]^S; reason: this is the vector c(f) of the argument after the theorem; on finite values the topology of [0, ∞] is that of ℝ
--   - reading: the chain is unichain → the matrix P(f) has exactly one closed communicating class; reason: a unichain has one recurrent class plus possibly transient states
--   - reading: an optimal policy (p. 287: ε-optimal for every ε > 0, for every initial distribution) → J(μ, f) ≤ J*(μ) + ε for every ε > 0 and every initial distribution μ; reason: the paper's definition
--   - encoding: J and c(f) as real or extended-real numbers → values in [0, ∞] (lintegrals of the nonnegative cost), compared in EReal where signed terms occur; reason: Lean convention; costs are nonnegative on K (Assumption 2.1), so the instances are the same and infinite values are represented exactly
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 298, Theorem 4.5 and the sentence after it; p. 293, §4.2 setting

import Mathlib
import Definitions.Def_ArapostathisAC_CanonicalTriplet_CMP
import Definitions.Def_ArapostathisAC_VanishingDiscount_Supplement_BorelCriteria
import Definitions.Def_ArapostathisAC_VanishingDiscount_Supplement_FiniteChain

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open ArapostathisAC.CanonicalTriplet

namespace ArapostathisAC.VanishingDiscount.Supplement

/-- Theorem 4.5 (p. 298). Finite state space `S` (discrete topology), compact metric action space
`A`. Let Assumptions 2.1 and 2.2 hold, assume that the cost vector `f ↦ c(f)` is continuous on
`Π_SR` (product of weak topologies on `∏_i 𝒫(A)`), and that under every `f ∈ Π_SR` the chain is
unichain. Then there is an optimal `f ∈ Π_SD`: `J(μ, f) ≤ J*(μ) + ε` for every `ε > 0` and every
initial distribution `μ`. -/
theorem theorem_4_5 {S A : Type*} [Fintype S] [DecidableEq S] [TopologicalSpace S]
    [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] [StandardBorelSpace S]
    [MetricSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : BorelCMP S A) (h22 : Assumption22 M)
    (hcont : ContinuousOn (srCost M) (srRules M))
    (huni : ∀ f : RandStationaryPolicy M, IsUnichain (srMatrix M f)) :
    ∃ f : StationaryPolicy M, IsAvgOptimalμ M f.toPolicy := by sorry

end ArapostathisAC.VanishingDiscount.Supplement
