-- Prove2me | Theorems.Thm_AvgCostLP_theorem_2_1
-- name    : AvgCostLP.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:31:41.929301+00:00
-- url     : https://prove2.me/theorems/584c052c-fe50-4efd-999f-dbb917eed14c
-- title:
--   Theorem 2.1 — optimality of stationary pairs; a stationary minimum pair exists
-- statement:
--   Let $\mathbb X$ be a Borel space and $\mathbb A$ a countable discrete action space, and consider an MDP model satisfying Assumption 2.1. Then:
--
--   1. for every policy $\pi\in\Pi$ and initial distribution $\zeta\in\mathcal P(\mathbb X)$ with $J(\pi,\zeta)<\infty$ there is a stationary pair $(\bar\mu,\bar p)\in\Delta_s$ with
--   $$J(\bar\mu,\bar p)\le J(\pi,\zeta);$$
--   2. there is a stationary minimum pair $(\mu^*,p^*)\in\Delta_s$, i.e. $J(\mu^*,p^*)=\rho^*$.
--
--   This reduces the history-dependent problem to stationary pairs and is the source of the primal program's solvability. The paper cites it from [40, Prop. 3.2, Thm. 3.3].
--
--   **Formalization Note** A stationary policy is evaluated as the policy $(\mu,\mu,\dots)\in\Pi$.
--
--   Differences from the source:
--   - generalization: X a Borel space: separable metrizable and homeomorphic to a Borel subset of a Polish space (p.4) → X metrizable and second countable with its Borel σ-algebra; reason: only the clause 'Borel subset of a Polish space' is dropped, so every Borel space of the paper is an instance (under (SU), X is σ-compact and the clause holds anyway)
--   - encoding: Borel measurable stochastic kernels: Borel maps into P(Y) with the weak topology (p.4) → Mathlib Markov kernels (measurable maps into probability measures); reason: the two notions agree on separable metrizable spaces [3, Props. 7.25-7.26]
--   - encoding: Borel measures on Γ → measures on X × A with γ(Γᶜ) = 0; reason: the paper identifies the two (p.9)
--   - encoding: costs c, J and ρ* in [0, +∞], expectations and ∫ c dγ → ℝ≥0∞ with lintegral; real objective values as toReal of finite lintegrals; reason: Lean convention; same instances
--   - encoding: indices j ∈ ℤ₊ of Γ_j → j : ℕ; reason: shift of the index; same sequences
--   - encoding: continuity / convergence in P(X) with the topology of weak convergence → continuity / convergence of ∫ f dμ for every bounded continuous f; reason: the weak topology is the coarsest making these maps continuous; same instances
-- source:
--   Yu, On Linear Programming for Constrained and Unconstrained Average-Cost Markov Decision Processes with Countable Action Spaces and Strictly Unbounded Costs, arXiv:1905.12095v3, Theorem 2.1, p.7

import Mathlib
import Definitions.Def_AvgCostLP_Assumption21
import Definitions.Def_AvgCostLP_IsStationaryPair
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace AvgCostLP

/-- Yu, On Linear Programming for Constrained and Unconstrained Average-Cost Markov Decision Processes with Countable Action Spaces and Strictly Unbounded Costs, arXiv:1905.12095v3, Theorem 2.1, p.7 (optimality of stationary pairs [40, Prop. 3.2, Thm. 3.3]). Under
Assumption 2.1:
(i) for any pair `(π, ζ) ∈ Π × P(X)` with `J(π, ζ) < ∞` there is a stationary pair
`(μ̄, p̄) ∈ Δ_s` with `J(μ̄, p̄) ≤ J(π, ζ)`;
(ii) there exists a stationary minimum pair `(μ*, p*) ∈ Δ_s`.

**Formalization Note** `X` is a Borel space, encoded as metrizable, second countable, with its Borel σ-algebra (the clause "homeomorphic to a Borel subset of a Polish space" is dropped); `A` is countable with the discrete topology and its Borel σ-algebra. Measures on `Γ` are measures on `X × A` concentrated on `Γ`; costs and `J` take values in `ℝ≥0∞`. A stationary policy enters `J` through its embedding
`μ.toPolicy` into `Π`. -/
theorem theorem_2_1 {X A : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A] [Countable A]
    (M : Model X A)
    (hM : Assumption21 M) :
    (∀ (π : Policy M) (ζ : ProbabilityMeasure X), avgCost M π ζ < ⊤ →
      ∃ (μ : StationaryPolicy M) (p : ProbabilityMeasure X),
        IsStationaryPair M μ p ∧ avgCost M μ.toPolicy p ≤ avgCost M π ζ) ∧
    ∃ (μ : StationaryPolicy M) (p : ProbabilityMeasure X), IsStationaryMinPair M μ p := by sorry

end AvgCostLP
