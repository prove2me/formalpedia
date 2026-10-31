-- Prove2me | Theorems.Thm_AvgCostLP_theorem_3_1
-- name    : AvgCostLP.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:31:21.872013+00:00
-- url     : https://prove2.me/theorems/3ee1e18b-0ce1-4315-b78a-e87a8d59f2b7
-- title:
--   Theorem 3.1 — (P) consistent and solvable, (P*) consistent, $\inf(P)=\sup(P^*)=\rho^*$
-- statement:
--   Let $\mathbb X$ be a Borel space and $\mathbb A$ a countable action space with the discrete topology, and consider an average-cost MDP with admissible action sets $A(x)$, transition kernel $q$ and cost $c\ge0$ satisfying Assumption 2.1 ((G), strictly unbounded costs (SU) and majorization (M)). Let $\rho^*$ be the minimum average cost over all policies and initial distributions. Then the linear programs (P) and (P*) of (3.10)–(3.11) satisfy:
--
--   1. (P) is consistent and solvable, and (P*) is consistent;
--   2. there is no duality gap:
--   $$\inf(\mathrm P)=\sup(\mathrm P^*)=\rho^* .$$
--
--   In particular $\rho^*$ is finite and attained by a feasible occupation measure, while $\sup(\mathrm P^*)$ need not be attained (Remark 3.3). Earlier results of this kind needed lower semicontinuous costs and weakly continuous kernels; Theorem 3.1 replaces them by the majorization condition (M).
--
--   **Formalization Note** The conclusion says: $\rho^*\ne+\infty$; $\rho^*$ is the least element of the set of primal objective values; the set of dual objective values is nonempty and has least upper bound $\rho^*$.
--
--   Differences from the source:
--   - generalization: X a Borel space: separable metrizable and homeomorphic to a Borel subset of a Polish space (p.4) → X metrizable and second countable with its Borel σ-algebra; reason: only the clause 'Borel subset of a Polish space' is dropped, so every Borel space of the paper is an instance (under (SU), X is σ-compact and the clause holds anyway)
--   - encoding: Borel measurable stochastic kernels: Borel maps into P(Y) with the weak topology (p.4) → Mathlib Markov kernels (measurable maps into probability measures); reason: the two notions agree on separable metrizable spaces [3, Props. 7.25-7.26]
--   - encoding: Borel measures on Γ → measures on X × A with γ(Γᶜ) = 0; reason: the paper identifies the two (p.9)
--   - encoding: costs c, J and ρ* in [0, +∞], expectations and ∫ c dγ → ℝ≥0∞ with lintegral; real objective values as toReal of finite lintegrals; reason: Lean convention; same instances
--   - encoding: the values inf(P), sup(P*) and the subvalue → IsLeast / IsLUB / IsGLB of the sets of objective values; reason: Lean convention; a real sInf/sSup would return 0 on empty or unbounded sets
--   - encoding: indices j ∈ ℤ₊ of Γ_j → j : ℕ; reason: shift of the index; same sequences
--   - encoding: continuity / convergence in P(X) with the topology of weak convergence → continuity / convergence of ∫ f dμ for every bounded continuous f; reason: the weak topology is the coarsest making these maps continuous; same instances
-- source:
--   Yu, On Linear Programming for Constrained and Unconstrained Average-Cost Markov Decision Processes with Countable Action Spaces and Strictly Unbounded Costs, arXiv:1905.12095v3, Theorem 3.1, p.12

import Mathlib
import Definitions.Def_AvgCostLP_Assumption21
import Definitions.Def_AvgCostLP_IsPrimalFeasible
import Definitions.Def_AvgCostLP_IsDualFeasible
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace AvgCostLP

/-- Yu, On Linear Programming for Constrained and Unconstrained Average-Cost Markov Decision Processes with Countable Action Spaces and Strictly Unbounded Costs, arXiv:1905.12095v3, Theorem 3.1, p.12 (consistency and absence of a duality gap). Under Assumption 2.1, the
linear programs (P) and (P*) in (3.10)–(3.11) satisfy:
(i) (P) is consistent and solvable, and (P*) is consistent;
(ii) there is no duality gap: `inf(P) = sup(P*) = ρ*`.

In Lean: `ρ*` is finite, `ρ*` is the least objective value of a feasible solution of (P) (so (P)
is consistent and solvable with `inf(P) = ρ*`), the set of dual objective values is nonempty
((P*) is consistent), and `ρ*` is its least upper bound (`sup(P*) = ρ*`).

**Formalization Note** `X` is a Borel space, encoded as metrizable, second countable, with its Borel σ-algebra (the clause "homeomorphic to a Borel subset of a Polish space" is dropped); `A` is countable with the discrete topology and its Borel σ-algebra. Measures on `Γ` are measures on `X × A` concentrated on `Γ`; costs and `J` take values in `ℝ≥0∞`. `ρ*` is the infimum over all randomized history-dependent
policies and all initial distributions. `IsLeast`/`IsLUB` are used instead of real `sInf`/`sSup`;
`sup(P*)` need not be attained (Remark 3.3), and is not asserted to be. -/
theorem theorem_3_1 {X A : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A] [Countable A]
    (M : Model X A)
    (hM : Assumption21 M) :
    minAvgCost M ≠ ⊤ ∧ IsLeast (primalValues M) (minAvgCost M).toReal ∧
      (dualValues M).Nonempty ∧ IsLUB (dualValues M) (minAvgCost M).toReal := by sorry

end AvgCostLP
