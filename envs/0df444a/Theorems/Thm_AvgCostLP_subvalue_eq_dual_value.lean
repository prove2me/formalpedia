-- Prove2me | Theorems.Thm_AvgCostLP_subvalue_eq_dual_value
-- name    : AvgCostLP.subvalue_eq_dual_value
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:31:08.637112+00:00
-- url     : https://prove2.me/theorems/f5b18cbb-b8ee-4b5a-b258-e2429dbec51f
-- title:
--   §5.1.1, p.20 — $\sup(P^*)$ is finite and equals the subvalue $\underline\rho$ of (P)
-- statement:
--   Let $\mathbb X$ be a Borel space and $\mathbb A$ countable and discrete, and assume Assumption 2.1. Since (P) and (P*) are consistent, Theorem 2.2 applies to (3.10)–(3.11) with $L^*$ of (3.8): there is a real number $\underline\rho$ which is both
--   $$\sup(\mathrm P^*)=\sup\{\rho\mid(\rho,h)\text{ feasible for (P*)}\}\quad\text{and}\quad\inf\{r\mid((1,0),r)\in\overline H\},$$
--   the subvalue of (P), where $\overline H$ is the closure of the set $H$ of (5.1) in $\sigma(\mathbb R\times\mathbb M(\mathbb X)\times\mathbb R,\ \mathbb R\times\mathbb F_b(\mathbb X)\times\mathbb R)$.
--
--   After this step, "no duality gap" reduces to $\underline\rho=\rho^*$.
--
--   Differences from the source:
--   - generalization: X a Borel space: separable metrizable and homeomorphic to a Borel subset of a Polish space (p.4) → X metrizable and second countable with its Borel σ-algebra; reason: only the clause 'Borel subset of a Polish space' is dropped, so every Borel space of the paper is an instance (under (SU), X is σ-compact and the clause holds anyway)
--   - encoding: Borel measurable stochastic kernels: Borel maps into P(Y) with the weak topology (p.4) → Mathlib Markov kernels (measurable maps into probability measures); reason: the two notions agree on separable metrizable spaces [3, Props. 7.25-7.26]
--   - encoding: Borel measures on Γ → measures on X × A with γ(Γᶜ) = 0; reason: the paper identifies the two (p.9)
--   - encoding: costs c, J and ρ* in [0, +∞], expectations and ∫ c dγ → ℝ≥0∞ with lintegral; real objective values as toReal of finite lintegrals; reason: Lean convention; same instances
--   - encoding: the values inf(P), sup(P*) and the subvalue → IsLeast / IsLUB / IsGLB of the sets of objective values; reason: Lean convention; a real sInf/sSup would return 0 on empty or unbounded sets
--   - encoding: indices j ∈ ℤ₊ of Γ_j → j : ℕ; reason: shift of the index; same sequences
--   - encoding: continuity / convergence in P(X) with the topology of weak convergence → continuity / convergence of ∫ f dμ for every bounded continuous f; reason: the weak topology is the coarsest making these maps continuous; same instances
--   - encoding: 𝕄(X), finite signed Borel measures, and ∫ h dζ → Mathlib SignedMeasure X and ∫ h dζ⁺ − ∫ h dζ⁻ via the Jordan decomposition; reason: same objects; real-valued signed measures are finite
--   - reading: the weak topology σ(·,·) of p.7 ('|⟨·, y⟩| continuous') → the coarsest topology making every pairing ⟨·, w⟩ continuous; reason: the usual weak topology, fixed by the net characterization on p.7
-- source:
--   Yu, On Linear Programming for Constrained and Unconstrained Average-Cost Markov Decision Processes with Countable Action Spaces and Strictly Unbounded Costs, arXiv:1905.12095v3, §5.1.1, p.20, with (3.8), p.11, and Theorem 2.2, p.9

import Mathlib
import Definitions.Def_AvgCostLP_Assumption21
import Definitions.Def_AvgCostLP_IsDualFeasible
import Definitions.Def_AvgCostLP_subvalueSet
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace AvgCostLP

/-- Yu, On Linear Programming for Constrained and Unconstrained Average-Cost Markov Decision Processes with Countable Action Spaces and Strictly Unbounded Costs, arXiv:1905.12095v3, §5.1.1, p.20 (Theorem 2.2 applied to (3.10)–(3.11), with `L*` of (3.8), p.11): since
(P) and (P*) are consistent, `sup(P*)` is finite and equals the subvalue
`ρ̲ = inf{r | ((1, 0), r) ∈ H̄}`, with `H` the set (5.1) and `H̄` its closure in
`σ(ℝ × M(X) × ℝ, ℝ × F_b(X) × ℝ)`.

In Lean: some real `ρ̲` is both the least upper bound of the dual objective values and the
greatest lower bound of `{r | ((1, 0), r) ∈ H̄}`.

**Formalization Note** `X` is a Borel space, encoded as metrizable, second countable, with its Borel σ-algebra (the clause "homeomorphic to a Borel subset of a Polish space" is dropped); `A` is countable with the discrete topology and its Borel σ-algebra. Measures on `Γ` are measures on `X × A` concentrated on `Γ`; costs and `J` take values in `ℝ≥0∞`. `M(X)` is `SignedMeasure X`, integrals of bounded Borel `h`
against it go through the Jordan decomposition. -/
theorem subvalue_eq_dual_value {X A : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A] [Countable A]
    (M : Model X A)
    (hM : Assumption21 M) :
    ∃ ρ : ℝ, IsLUB (dualValues M) ρ ∧ IsGLB (subvalueSet M) ρ := by sorry

end AvgCostLP
