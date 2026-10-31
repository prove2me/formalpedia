-- Prove2me | Theorems.Thm_AvgCostLP_primal_solvable_weak_duality
-- name    : AvgCostLP.primal_solvable_weak_duality
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:31:28.243573+00:00
-- url     : https://prove2.me/theorems/8a449aa3-2c2c-49eb-bd10-02b1ded16583
-- title:
--   §3.1, p.11 — (P) consistent and solvable, $(0,0)$ dual feasible, $0\le\sup(P^*)\le\inf(P)=\rho^*$
-- statement:
--   Let $\mathbb X$ be a Borel space and $\mathbb A$ countable and discrete, and assume Assumption 2.1. Then:
--
--   1. $\rho^*<\infty$, and $\rho^*$ is the least objective value $\int c\,d\gamma$ over the feasible solutions $\gamma$ of (P); so (P) is consistent and solvable and $\inf(\mathrm P)=\rho^*$;
--   2. $(\rho,h)=(0,0)$ is feasible for (P*), since $c\ge0$;
--   3. weak duality: every feasible value $\rho$ of (P*) is at most every feasible value $\int c\,d\gamma$ of (P).
--
--   Together, $0\le\sup(\mathrm P^*)\le\inf(\mathrm P)=\rho^*$.
--
--   Differences from the source:
--   - generalization: X a Borel space: separable metrizable and homeomorphic to a Borel subset of a Polish space (p.4) → X metrizable and second countable with its Borel σ-algebra; reason: only the clause 'Borel subset of a Polish space' is dropped, so every Borel space of the paper is an instance (under (SU), X is σ-compact and the clause holds anyway)
--   - encoding: Borel measurable stochastic kernels: Borel maps into P(Y) with the weak topology (p.4) → Mathlib Markov kernels (measurable maps into probability measures); reason: the two notions agree on separable metrizable spaces [3, Props. 7.25-7.26]
--   - encoding: Borel measures on Γ → measures on X × A with γ(Γᶜ) = 0; reason: the paper identifies the two (p.9)
--   - encoding: costs c, J and ρ* in [0, +∞], expectations and ∫ c dγ → ℝ≥0∞ with lintegral; real objective values as toReal of finite lintegrals; reason: Lean convention; same instances
--   - encoding: the values inf(P), sup(P*) and the subvalue → IsLeast / IsLUB / IsGLB of the sets of objective values; reason: Lean convention; a real sInf/sSup would return 0 on empty or unbounded sets
--   - encoding: indices j ∈ ℤ₊ of Γ_j → j : ℕ; reason: shift of the index; same sequences
--   - encoding: continuity / convergence in P(X) with the topology of weak convergence → continuity / convergence of ∫ f dμ for every bounded continuous f; reason: the weak topology is the coarsest making these maps continuous; same instances
--   - encoding: 0 ≤ sup(P*) ≤ inf(P) → (0, 0) is dual feasible, and every dual objective value is at most every primal objective value; reason: with both sets nonempty the two forms are equivalent
-- source:
--   Yu, On Linear Programming for Constrained and Unconstrained Average-Cost Markov Decision Processes with Countable Action Spaces and Strictly Unbounded Costs, arXiv:1905.12095v3, §3.1, p.11

import Mathlib
import Definitions.Def_AvgCostLP_Assumption21
import Definitions.Def_AvgCostLP_IsPrimalFeasible
import Definitions.Def_AvgCostLP_IsDualFeasible
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace AvgCostLP

/-- Yu, On Linear Programming for Constrained and Unconstrained Average-Cost Markov Decision Processes with Countable Action Spaces and Strictly Unbounded Costs, arXiv:1905.12095v3, §3.1, p.11: under Assumption 2.1, the existence of a stationary minimum pair ensures
that (P) is consistent and solvable; the dual program (P*) is consistent, since `c ≥ 0` makes
`ρ = 0`, `h ≡ 0` feasible; and `0 ≤ sup(P*) ≤ inf(P) = ρ*`.

In Lean: `ρ*` is finite and is the least objective value of (P); `(0, 0)` is feasible for (P*);
and every dual objective value is at most every primal objective value (weak duality).

**Formalization Note** `X` is a Borel space, encoded as metrizable, second countable, with its Borel σ-algebra (the clause "homeomorphic to a Borel subset of a Polish space" is dropped); `A` is countable with the discrete topology and its Borel σ-algebra. Measures on `Γ` are measures on `X × A` concentrated on `Γ`; costs and `J` take values in `ℝ≥0∞`. -/
theorem primal_solvable_weak_duality {X A : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A] [Countable A]
    (M : Model X A)
    (hM : Assumption21 M) :
    minAvgCost M ≠ ⊤ ∧ IsLeast (primalValues M) (minAvgCost M).toReal ∧
      IsDualFeasible M 0 (fun _ => 0) ∧
      ∀ ρ ∈ dualValues M, ∀ r ∈ primalValues M, ρ ≤ r := by sorry

end AvgCostLP
