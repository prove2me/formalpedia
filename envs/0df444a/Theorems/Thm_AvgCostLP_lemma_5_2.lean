-- Prove2me | Theorems.Thm_AvgCostLP_lemma_5_2
-- name    : AvgCostLP.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:29:20.972198+00:00
-- url     : https://prove2.me/theorems/4acb2cb6-7bb4-49cc-beb1-12a1e71eb55c
-- title:
--   Lemma 5.2 — a sequence $\{\gamma_n\}\subset\{\gamma_i\}$ with (5.7)–(5.8)
-- statement:
--   Let $\mathbb X$ be a Borel space and $\mathbb A$ countable and discrete. Let $\{\gamma_i\}_{i\in I}$ be a net over a directed set, of measures on $\mathbb X\times\mathbb A$, satisfying (5.3) for all $h\in\mathbb F_b(\mathbb X)$ and $\langle\gamma_i,c\rangle\to\underline\rho$ (5.4), and let $\mathcal H\subset\mathbb F_b(\mathbb X)$ be countable (in the paper $\mathcal H=\hat C_b(\mathbb X)\cup\hat F_b(\mathbb X)$). Then there is a sequence $\{\gamma_n\}_{n\ge0}\subset\{\gamma_i\}_{i\in I}$ such that
--   $$\int_{\mathbb X}h(x)\,\hat\gamma_n(dx)-\int_\Gamma\int_{\mathbb X}h(y)\,q(dy\mid x,a)\,\gamma_n(d(x,a))\to0\quad\forall h\in\mathcal H, \tag{5.7}$$
--   $$\langle\gamma_n,c\rangle\to\underline\rho. \tag{5.8}$$
--
--   The sequence replaces the net so that Prohorov's theorem can be applied in Step (iii).
--
--   Differences from the source:
--   - generalization: X a Borel space: separable metrizable and homeomorphic to a Borel subset of a Polish space (p.4) → X metrizable and second countable with its Borel σ-algebra; reason: only the clause 'Borel subset of a Polish space' is dropped, so every Borel space of the paper is an instance (under (SU), X is σ-compact and the clause holds anyway)
--   - encoding: Borel measurable stochastic kernels: Borel maps into P(Y) with the weak topology (p.4) → Mathlib Markov kernels (measurable maps into probability measures); reason: the two notions agree on separable metrizable spaces [3, Props. 7.25-7.26]
--   - encoding: Borel measures on Γ → measures on X × A with γ(Γᶜ) = 0; reason: the paper identifies the two (p.9)
--   - encoding: costs c, J and ρ* in [0, +∞], expectations and ∫ c dγ → ℝ≥0∞ with lintegral; real objective values as toReal of finite lintegrals; reason: Lean convention; same instances
--   - generalization: the net of Step (i) and the family Ĉ_b(X) ∪ F̂_b(X) → any directed net satisfying (5.3) and (5.4), and any countable family of bounded Borel functions; reason: the net of Step (i) satisfies (5.3)-(5.4) and Ĉ_b(X) ∪ F̂_b(X) is a countable subset of F_b(X), so the statement specializes to the page's
--   - generalization: ρ̲ in (5.4) is the subvalue of (P) → ρ any real number that is the limit of ⟨γ, c⟩ along the net; reason: the argument uses only the convergence; the subvalue is such a limit, so the statement specializes to the page's
-- source:
--   Yu, On Linear Programming for Constrained and Unconstrained Average-Cost Markov Decision Processes with Countable Action Spaces and Strictly Unbounded Costs, arXiv:1905.12095v3, Lemma 5.2, p.22

import Mathlib
import Definitions.Def_AvgCostLP_IsPrimalFeasible
import Definitions.Def_AvgCostLP_IsDualFeasible
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace AvgCostLP

/-- Yu, On Linear Programming for Constrained and Unconstrained Average-Cost Markov Decision Processes with Countable Action Spaces and Strictly Unbounded Costs, arXiv:1905.12095v3, Lemma 5.2, p.22: there exists a sequence `{γ_n}_{n ≥ 0} ⊂ {γ_i}_{i ∈ I}` such
that
`∫ h dγ̂_n − ∫_Γ ∫_X h(y) q(dy | x, a) γ_n(d(x, a)) → 0` for all `h ∈ Ĉ_b(X) ∪ F̂_b(X)` (5.7)
and `⟨γ_n, c⟩ → ρ̲` (5.8).

In Lean: for any directed net satisfying (5.3) and (5.4) and any countable family `𝓗` of bounded
Borel functions (the paper's `Ĉ_b(X) ∪ F̂_b(X)`), some sequence `n ↦ γ_{i_n}` from the net
satisfies (5.7) on `𝓗` and (5.8).

**Formalization Note** `X` is a Borel space, encoded as metrizable, second countable, with its Borel σ-algebra (the clause "homeomorphic to a Borel subset of a Polish space" is dropped); `A` is countable with the discrete topology and its Borel σ-algebra. Measures on `Γ` are measures on `X × A` concentrated on `Γ`; costs and `J` take values in `ℝ≥0∞`. -/
theorem lemma_5_2 {X A : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A] [Countable A]
    (M : Model X A)
    {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (γ : I → Measure (X × A)) (ρ : ℝ)
    (h53 : ∀ h : X → ℝ, IsBoundedBorel h → Tendsto (fun i => residual M (γ i) h) atTop (𝓝 0))
    (h54 : Tendsto (fun i => (∫⁻ p, M.c p ∂(γ i)).toReal) atTop (𝓝 ρ))
    (H : Set (X → ℝ)) (hH : H.Countable) (hHb : ∀ h ∈ H, IsBoundedBorel h) :
    ∃ i : ℕ → I, (∀ h ∈ H, Tendsto (fun n => residual M (γ (i n)) h) atTop (𝓝 0)) ∧
      Tendsto (fun n => (∫⁻ p, M.c p ∂(γ (i n))).toReal) atTop (𝓝 ρ) := by sorry

end AvgCostLP
