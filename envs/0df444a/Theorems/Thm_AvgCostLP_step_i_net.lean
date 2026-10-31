-- Prove2me | Theorems.Thm_AvgCostLP_step_i_net
-- name    : AvgCostLP.step_i_net
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:30:26.981032+00:00
-- url     : https://prove2.me/theorems/720a76e8-3a9a-4144-b250-55a240440646
-- title:
--   §5.1.1, Step (i), (5.2)–(5.4) — a net of probability measures on $\Gamma$ reaching the subvalue
-- statement:
--   Let $\mathbb X$ be a Borel space and $\mathbb A$ countable and discrete, and let $\underline\rho$ be the (finite) subvalue of (P), $\underline\rho=\inf\{r\mid((1,0),r)\in\overline H\}$. Then $((1,0),\underline\rho)\in\overline H$, and there is a directed set $I$ and a net $\{\gamma_i\}_{i\in I}$ of probability measures on $\Gamma$ with $\int(1+c)\,d\gamma_i<\infty$ such that
--   $$\int_{\mathbb X}h(x)\,\hat\gamma_i(dx)-\int_\Gamma\int_{\mathbb X}h(y)\,q(dy\mid x,a)\,\gamma_i(d(x,a))\to0\quad\forall h\in\mathbb F_b(\mathbb X), \tag{5.3}$$
--   $$\langle\gamma_i,c\rangle\to\underline\rho. \tag{5.4}$$
--
--   This is the net $\{\gamma_i\}$ with $(L\gamma_i,\langle\gamma_i,c\rangle)\to((1,0),\underline\rho)$ of Step (i), after the normalization $\gamma_i(\cdot)/\gamma_i(\Gamma)$ permitted by (5.2).
--
--   **Formalization Note** The index set lives in the universe of $\mathbb X$.
--
--   Differences from the source:
--   - generalization: X a Borel space: separable metrizable and homeomorphic to a Borel subset of a Polish space (p.4) → X metrizable and second countable with its Borel σ-algebra; reason: only the clause 'Borel subset of a Polish space' is dropped, so every Borel space of the paper is an instance (under (SU), X is σ-compact and the clause holds anyway)
--   - encoding: Borel measurable stochastic kernels: Borel maps into P(Y) with the weak topology (p.4) → Mathlib Markov kernels (measurable maps into probability measures); reason: the two notions agree on separable metrizable spaces [3, Props. 7.25-7.26]
--   - encoding: Borel measures on Γ → measures on X × A with γ(Γᶜ) = 0; reason: the paper identifies the two (p.9)
--   - encoding: costs c, J and ρ* in [0, +∞], expectations and ∫ c dγ → ℝ≥0∞ with lintegral; real objective values as toReal of finite lintegrals; reason: Lean convention; same instances
--   - encoding: the values inf(P), sup(P*) and the subvalue → IsLeast / IsLUB / IsGLB of the sets of objective values; reason: Lean convention; a real sInf/sSup would return 0 on empty or unbounded sets
--   - generalization: Step (i) inside the proof of Theorem 3.1, under Assumption 2.1 → no Assumption 2.1; only that ρ̲ is the greatest lower bound of {r | ((1, 0), r) ∈ H̄}; reason: the step uses only that the subvalue is finite; under Assumption 2.1 it is (Theorem 2.2), so the statement specializes to the page's
--   - encoding: 𝕄(X), the weak topology σ(ℝ × 𝕄(X) × ℝ, ℝ × F_b(X) × ℝ) → SignedMeasure X with the topology induced by the pairings; reason: same objects and the usual weak topology (p.7)
--   - encoding: a net over a directed set I with (5.2), then normalized so that γ_i(Γ) = 1 → the normalized net only, over an index type in the universe of X; reason: (5.2) is immediate for probability measures, and the paper's closure is reached by nets indexed by finite subsets of ℝ × F_b(X) × ℝ and accuracies, which live in that universe
-- source:
--   Yu, On Linear Programming for Constrained and Unconstrained Average-Cost Markov Decision Processes with Countable Action Spaces and Strictly Unbounded Costs, arXiv:1905.12095v3, §5.1.1, Step (i), (5.2)-(5.4), p.20

import Mathlib
import Definitions.Def_AvgCostLP_IsPrimalFeasible
import Definitions.Def_AvgCostLP_subvalueSet
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace AvgCostLP

universe u

/-- Yu, On Linear Programming for Constrained and Unconstrained Average-Cost Markov Decision Processes with Countable Action Spaces and Strictly Unbounded Costs, arXiv:1905.12095v3, §5.1.1, Step (i), (5.2)–(5.4), p.20: let `ρ̲` be the subvalue of (P). Then
`((1, 0), ρ̲) ∈ H̄`, and there is a net `{γ_i}_{i ∈ I}` in `M⁺_w(Γ)` with
`(Lγ_i, ⟨γ_i, c⟩) → ((1, 0), ρ̲)`, i.e. `γ_i(Γ) → 1` (5.2),
`∫ h dγ̂_i − ∫_Γ ∫_X h(y) q(dy | x, a) γ_i(d(x, a)) → 0` for all `h ∈ F_b(X)` (5.3) and
`⟨γ_i, c⟩ → ρ̲` (5.4); after normalizing, every `γ_i` is a probability measure on `Γ`.

In Lean: `ρ̲ ∈ {r | ((1, 0), r) ∈ H̄}`, and the net after normalization: a directed net of
probability measures `γ_i` on `Γ` with `∫ w dγ_i < ∞`, (5.3) and (5.4).

**Formalization Note** `X` is a Borel space, encoded as metrizable, second countable, with its Borel σ-algebra (the clause "homeomorphic to a Borel subset of a Polish space" is dropped); `A` is countable with the discrete topology and its Borel σ-algebra. Measures on `Γ` are measures on `X × A` concentrated on `Γ`; costs and `J` take values in `ℝ≥0∞`. The index set lives in the universe of `X`. Assumption 2.1
is not needed for this step and is not assumed; the subvalue is given as a greatest lower bound. -/
theorem step_i_net {X : Type u} {A : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A] [Countable A]
    (M : Model X A)
    (ρ : ℝ) (hρ : IsGLB (subvalueSet M) ρ) :
    ρ ∈ subvalueSet M ∧ ∃ (I : Type u) (_ : Preorder I), IsDirected I (· ≤ ·) ∧ Nonempty I ∧
      ∃ γ : I → Measure (X × A),
        (∀ i, IsProbabilityMeasure (γ i) ∧ γ i M.graphᶜ = 0 ∧ ∫⁻ p, (1 + M.c p) ∂(γ i) < ⊤) ∧
        (∀ h : X → ℝ, IsBoundedBorel h → Tendsto (fun i => residual M (γ i) h) atTop (𝓝 0)) ∧
        Tendsto (fun i => (∫⁻ p, M.c p ∂(γ i)).toReal) atTop (𝓝 ρ) := by sorry

end AvgCostLP
