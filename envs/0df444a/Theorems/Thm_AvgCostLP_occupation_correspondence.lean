-- Prove2me | Theorems.Thm_AvgCostLP_occupation_correspondence
-- name    : AvgCostLP.occupation_correspondence
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:31:36.556873+00:00
-- url     : https://prove2.me/theorems/b9c9a8df-438a-4d42-9fa7-396d0e3b0276
-- title:
--   §3.1, (3.1)–(3.4) — stationary pairs ↔ probability measures on $\Gamma$ satisfying (3.1)
-- statement:
--   Let $\mathbb X$ be a Borel space and $\mathbb A$ countable and discrete.
--
--   1. If $(\mu,p)\in\Delta_s$, then $\gamma(d(x,a))=\mu(da\mid x)\,p(dx)$ (3.2) is a probability measure on $\Gamma$ satisfying
--   $$\hat\gamma(B)=\int_\Gamma q(B\mid x,a)\,\gamma(d(x,a))\qquad\forall B\in\mathcal B(\mathbb X), \tag{3.1}$$
--   and $J(\mu,p)=\int c\,d\gamma$ (3.3). If moreover $J(\mu,p)<\infty$, then $\gamma$ is feasible for (P).
--   2. Conversely, if $\gamma$ is a probability measure on $\Gamma$ satisfying (3.1), then $\gamma(d(x,a))=\mu(da\mid x)\,p(dx)$ with $p=\hat\gamma$ for some stationary policy $\mu$ obeying the control constraint, and every such $(\mu,p)$ is a stationary pair with $J(\mu,p)=\int c\,d\gamma$.
--
--   Hence minimizing $\int c\,d\gamma$ over the probability measures satisfying (3.1) ("ergodic occupation measures") is the same as finding a stationary minimum pair.
--
--   Differences from the source:
--   - generalization: X a Borel space: separable metrizable and homeomorphic to a Borel subset of a Polish space (p.4) → X metrizable and second countable with its Borel σ-algebra; reason: only the clause 'Borel subset of a Polish space' is dropped, so every Borel space of the paper is an instance (under (SU), X is σ-compact and the clause holds anyway)
--   - encoding: Borel measurable stochastic kernels: Borel maps into P(Y) with the weak topology (p.4) → Mathlib Markov kernels (measurable maps into probability measures); reason: the two notions agree on separable metrizable spaces [3, Props. 7.25-7.26]
--   - encoding: Borel measures on Γ → measures on X × A with γ(Γᶜ) = 0; reason: the paper identifies the two (p.9)
--   - encoding: costs c, J and ρ* in [0, +∞], expectations and ∫ c dγ → ℝ≥0∞ with lintegral; real objective values as toReal of finite lintegrals; reason: Lean convention; same instances
-- source:
--   Yu, On Linear Programming for Constrained and Unconstrained Average-Cost Markov Decision Processes with Countable Action Spaces and Strictly Unbounded Costs, arXiv:1905.12095v3, §3.1, (3.1)-(3.4), pp.9-10

import Mathlib
import Definitions.Def_AvgCostLP_IsStationaryPair
import Definitions.Def_AvgCostLP_IsPrimalFeasible
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace AvgCostLP

/-- Yu, On Linear Programming for Constrained and Unconstrained Average-Cost Markov Decision Processes with Countable Action Spaces and Strictly Unbounded Costs, arXiv:1905.12095v3, §3.1, (3.1)–(3.4), pp.9–10: the correspondence between stationary pairs and
probability measures on `Γ` satisfying (3.1).

(a) If `(μ, p) ∈ Δ_s`, then `γ(d(x, a)) = μ(da | x) p(dx)` (3.2) is a probability measure on `Γ`
satisfying (3.1), `γ̂(B) = ∫_Γ q(B | x, a) γ(d(x, a))` for all Borel `B`, and
`J(μ, p) = ∫ c dγ` (3.3); if moreover `J(μ, p) < ∞`, then `γ` is a feasible solution of (P).

(b) Conversely, a probability measure `γ` on `Γ` satisfying (3.1) decomposes as in (3.2),
`γ = μ ⊗ p` with `p = γ̂` and `μ` a stationary policy obeying the control constraint; and for every
such decomposition, `(μ, p)` is a stationary pair with `J(μ, p) = ∫ c dγ`.

**Formalization Note** `X` is a Borel space, encoded as metrizable, second countable, with its Borel σ-algebra (the clause "homeomorphic to a Borel subset of a Polish space" is dropped); `A` is countable with the discrete topology and its Borel σ-algebra. Measures on `Γ` are measures on `X × A` concentrated on `Γ`; costs and `J` take values in `ℝ≥0∞`. `γ = μ ⊗ p` is Mathlib's `p ⊗ₘ μ`; the stationary policy
obeys the control constraint at every state, not only `p`-a.e. -/
theorem occupation_correspondence {X A : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A] [Countable A]
    (M : Model X A) :
    (∀ (μ : StationaryPolicy M) (p : ProbabilityMeasure X), IsStationaryPair M μ p →
      ((p : Measure X) ⊗ₘ μ.kernel) M.graphᶜ = 0 ∧ ((p : Measure X) ⊗ₘ μ.kernel) M.graph = 1 ∧
      (∀ B : Set X, MeasurableSet B → ((p : Measure X) ⊗ₘ μ.kernel).map Prod.fst B =
        ∫⁻ z, M.q z B ∂((p : Measure X) ⊗ₘ μ.kernel)) ∧
      avgCost M μ.toPolicy p = ∫⁻ z, M.c z ∂((p : Measure X) ⊗ₘ μ.kernel) ∧
      (avgCost M μ.toPolicy p < ⊤ → IsPrimalFeasible M ((p : Measure X) ⊗ₘ μ.kernel))) ∧
    (∀ γ : Measure (X × A), IsProbabilityMeasure γ → γ M.graphᶜ = 0 →
      (∀ B : Set X, MeasurableSet B → γ.map Prod.fst B = ∫⁻ z, M.q z B ∂γ) →
      ∃ p : ProbabilityMeasure X, (p : Measure X) = γ.map Prod.fst ∧
        (∃ μ : StationaryPolicy M, γ = (p : Measure X) ⊗ₘ μ.kernel) ∧
        ∀ μ : StationaryPolicy M, γ = (p : Measure X) ⊗ₘ μ.kernel →
          IsStationaryPair M μ p ∧ avgCost M μ.toPolicy p = ∫⁻ z, M.c z ∂γ) := by sorry

end AvgCostLP
