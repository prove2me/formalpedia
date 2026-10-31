-- Prove2me | Theorems.Thm_AvgCostLP_lemma_5_3
-- name    : AvgCostLP.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:29:18.653479+00:00
-- url     : https://prove2.me/theorems/ec227aed-ca19-44eb-a694-f51648c3d1f7
-- title:
--   Lemma 5.3 — majorization passes to $\hat\gamma_n$ and to $\bar p$
-- statement:
--   Let $\mathbb X$ be a Borel space and $\mathbb A$ countable and discrete. Let $O\subset\mathbb X$ be open, $D\subset\mathbb X$ closed and $\nu$ a finite measure satisfying the majorization (2.1), and let $B\subset\mathbb X$ be closed; put $E=(O\setminus D)\cap B^c$. Let $\gamma_n$ be probability measures on $\Gamma$ satisfying (5.7) for $h=\mathbb 1_E$, whose marginals converge weakly, $\hat\gamma_n\xrightarrow{w}\bar p$. Then
--   $$\limsup_{n\to\infty}\hat\gamma_n\big((O\setminus D)\cap B^c\big)\le\nu(B^c),\qquad\bar p\big((O\setminus D)\cap B^c\big)\le\nu(B^c).$$
--
--   In the paper this holds for every $(O,D,\nu,B)\in\mathcal W_1\cup\mathcal W_2$; it is what controls the parts of the model where $c^m$ and $q$ are not continuous.
--
--   Differences from the source:
--   - generalization: X a Borel space: separable metrizable and homeomorphic to a Borel subset of a Polish space (p.4) → X metrizable and second countable with its Borel σ-algebra; reason: only the clause 'Borel subset of a Polish space' is dropped, so every Borel space of the paper is an instance (under (SU), X is σ-compact and the clause holds anyway)
--   - encoding: Borel measurable stochastic kernels: Borel maps into P(Y) with the weak topology (p.4) → Mathlib Markov kernels (measurable maps into probability measures); reason: the two notions agree on separable metrizable spaces [3, Props. 7.25-7.26]
--   - encoding: Borel measures on Γ → measures on X × A with γ(Γᶜ) = 0; reason: the paper identifies the two (p.9)
--   - encoding: costs c, J and ρ* in [0, +∞], expectations and ∫ c dγ → ℝ≥0∞ with lintegral; real objective values as toReal of finite lintegrals; reason: Lean convention; same instances
--   - encoding: continuity / convergence in P(X) with the topology of weak convergence → continuity / convergence of ∫ f dμ for every bounded continuous f; reason: the weak topology is the coarsest making these maps continuous; same instances
--   - generalization: (O, D, ν, B) ∈ W₁ ∪ W₂ and the sequence of Steps (ii)-(iii) → any open O, closed D, finite ν with (2.1), any closed B, and any sequence of probability measures on Γ with (5.7) for 1_E and γ̂_n → p̄ weakly; reason: every element of W₁ ∪ W₂ has these properties (O_j open, D_j closed, (2.1) by (M), B closed by Lemma 5.1), 1_E ∈ F̂_b(X), and γ_n → γ̄ gives γ̂_n → p̄
-- source:
--   Yu, On Linear Programming for Constrained and Unconstrained Average-Cost Markov Decision Processes with Countable Action Spaces and Strictly Unbounded Costs, arXiv:1905.12095v3, Lemma 5.3, p.22

import Mathlib
import Definitions.Def_AvgCostLP_IsPrimalFeasible
import Definitions.Def_AvgCostLP_TendstoWeakly
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace AvgCostLP

/-- Yu, On Linear Programming for Constrained and Unconstrained Average-Cost Markov Decision Processes with Countable Action Spaces and Strictly Unbounded Costs, arXiv:1905.12095v3, Lemma 5.3, p.22: for every `(O, D, ν, B) ∈ W₁ ∪ W₂`,
`limsup_{n→∞} γ̂_n((O \ D) ∩ Bᶜ) ≤ ν(Bᶜ)` and `p̄((O \ D) ∩ Bᶜ) ≤ ν(Bᶜ)`.

In Lean: for any open `O`, closed `D`, finite `ν` satisfying the majorization (2.1), any closed `B`,
and any sequence of probability measures `γ_n` on `Γ` satisfying (5.7) for `h = 1_E`,
`E = (O \ D) ∩ Bᶜ`, whose marginals converge weakly to `p̄`.

**Formalization Note** `X` is a Borel space, encoded as metrizable, second countable, with its Borel σ-algebra (the clause "homeomorphic to a Borel subset of a Polish space" is dropped); `A` is countable with the discrete topology and its Borel σ-algebra. Measures on `Γ` are measures on `X × A` concentrated on `Γ`; costs and `J` take values in `ℝ≥0∞`. -/
theorem lemma_5_3 {X A : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A] [Countable A]
    (M : Model X A)
    (O D : Set X) (ν : Measure X) [IsFiniteMeasure ν] (hO : IsOpen O) (hD : IsClosed D)
    (h21 : ∀ B : Set X, MeasurableSet B → ∀ p ∈ M.graph, M.q p ((O \ D) ∩ B) ≤ ν B)
    (B : Set X) (hB : IsClosed B) (γ : ℕ → Measure (X × A))
    (hγ : ∀ n, IsProbabilityMeasure (γ n) ∧ γ n M.graphᶜ = 0)
    (h57 : Tendsto (fun n => residual M (γ n) (((O \ D) ∩ Bᶜ).indicator 1)) atTop (𝓝 0))
    (pbar : Measure X) [IsProbabilityMeasure pbar]
    (hconv : TendstoWeakly (fun n => (γ n).map Prod.fst) pbar) :
    limsup (fun n => (γ n).map Prod.fst ((O \ D) ∩ Bᶜ)) atTop ≤ ν Bᶜ ∧
      pbar ((O \ D) ∩ Bᶜ) ≤ ν Bᶜ := by sorry

end AvgCostLP
