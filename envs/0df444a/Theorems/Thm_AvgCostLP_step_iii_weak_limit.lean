-- Prove2me | Theorems.Thm_AvgCostLP_step_iii_weak_limit
-- name    : AvgCostLP.step_iii_weak_limit
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:31:19.224454+00:00
-- url     : https://prove2.me/theorems/89ca67f0-1b59-4f82-909e-932e633c7cd2
-- title:
--   §5.1.1, Step (iii) — tightness, a weak limit $\bar\gamma$ on $\Gamma$ and $\bar\gamma=\bar\mu\otimes\bar p$
-- statement:
--   Let $\mathbb X$ be a Borel space and $\mathbb A$ countable and discrete, and let $\Gamma_j$ be a sequence as in Assumption 2.1(SU). Let $\{\gamma_n\}$ be probability measures on $\Gamma$ with $\int(1+c)\,d\gamma_n<\infty$ and $\langle\gamma_n,c\rangle\to\underline\rho$ (5.8). Then $\{\gamma_n\}$ is tight, and a subsequence converges weakly to a probability measure $\bar\gamma$ on $\mathcal B(\Gamma)$; moreover $\bar\gamma$ decomposes into its marginal $\bar p$ on $\mathbb X$ and a stochastic kernel $\bar\mu$ on $\mathbb A$ given $\mathbb X$ obeying the control constraint,
--   $$\bar\gamma(d(x,a))=\bar\mu(da\mid x)\,\bar p(dx).$$
--
--   This yields the candidate stationary pair $(\bar\mu,\bar p)$. $\Gamma$ need not be closed, and the limit still lives on $\Gamma$.
--
--   Differences from the source:
--   - generalization: X a Borel space: separable metrizable and homeomorphic to a Borel subset of a Polish space (p.4) → X metrizable and second countable with its Borel σ-algebra; reason: only the clause 'Borel subset of a Polish space' is dropped, so every Borel space of the paper is an instance (under (SU), X is σ-compact and the clause holds anyway)
--   - encoding: Borel measurable stochastic kernels: Borel maps into P(Y) with the weak topology (p.4) → Mathlib Markov kernels (measurable maps into probability measures); reason: the two notions agree on separable metrizable spaces [3, Props. 7.25-7.26]
--   - encoding: Borel measures on Γ → measures on X × A with γ(Γᶜ) = 0; reason: the paper identifies the two (p.9)
--   - encoding: costs c, J and ρ* in [0, +∞], expectations and ∫ c dγ → ℝ≥0∞ with lintegral; real objective values as toReal of finite lintegrals; reason: Lean convention; same instances
--   - encoding: indices j ∈ ℤ₊ of Γ_j → j : ℕ; reason: shift of the index; same sequences
--   - generalization: the sequence of Lemma 5.2 and Assumption 2.1 → any sequence of probability measures on Γ with ∫ w dγ_n < ∞ and (5.8), and only (SU); reason: the page invokes only (5.8) and (SU); the sequence of Lemma 5.2 has these properties
--   - encoding: weak convergence in P(Γ) → weak convergence on X × A tested with bounded continuous functions on X × A; reason: for measures concentrated on Γ the two coincide (portmanteau with the relatively closed sets F ∩ Γ)
--   - generalization: ρ̲ in (5.8) is the subvalue of (P) → ρ any real number that is the limit of ⟨γ, c⟩ along the sequence; reason: the argument uses only the convergence; the subvalue is such a limit, so the statement specializes to the page's
-- source:
--   Yu, On Linear Programming for Constrained and Unconstrained Average-Cost Markov Decision Processes with Countable Action Spaces and Strictly Unbounded Costs, arXiv:1905.12095v3, §5.1.1, Step (iii), p.22

import Mathlib
import Definitions.Def_AvgCostLP_Assumption21
import Definitions.Def_AvgCostLP_IsPrimalFeasible
import Definitions.Def_AvgCostLP_TendstoWeakly
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace AvgCostLP

/-- Yu, On Linear Programming for Constrained and Unconstrained Average-Cost Markov Decision Processes with Countable Action Spaces and Strictly Unbounded Costs, arXiv:1905.12095v3, §5.1.1, Step (iii), p.22: (5.8) together with Assumption 2.1(SU) implies that
`{γ_n}` is a tight family of probability measures on `B(Γ)`, so by Prohorov's theorem a
subsequence converges weakly to a probability measure `γ̄` on `B(Γ)`; by [3, Cor. 7.27.2], `γ̄`
decomposes into its marginal `p̄` on `X` and a stochastic kernel `μ̄` on `A` given `X` obeying the
control constraint, `γ̄(d(x, a)) = μ̄(da | x) p̄(dx)`.

**Formalization Note** `X` is a Borel space, encoded as metrizable, second countable, with its Borel σ-algebra (the clause "homeomorphic to a Borel subset of a Polish space" is dropped); `A` is countable with the discrete topology and its Borel σ-algebra. Measures on `Γ` are measures on `X × A` concentrated on `Γ`; costs and `J` take values in `ℝ≥0∞`. Weak convergence is tested with bounded continuous functions
on `X × A`; for measures concentrated on `Γ` this is equivalent to weak convergence in `P(Γ)`
(portmanteau with relatively closed sets `F ∩ Γ`). `Γ` is not assumed closed. -/
theorem step_iii_weak_limit {X A : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A] [Countable A]
    (M : Model X A)
    (Γs : ℕ → Set (X × A)) (hSU : IsSUSeq M Γs) (γ : ℕ → Measure (X × A)) (ρ : ℝ)
    (hγ : ∀ n, IsProbabilityMeasure (γ n) ∧ γ n M.graphᶜ = 0 ∧ ∫⁻ p, (1 + M.c p) ∂(γ n) < ⊤)
    (h58 : Tendsto (fun n => (∫⁻ p, M.c p ∂(γ n)).toReal) atTop (𝓝 ρ)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ γbar : Measure (X × A), IsProbabilityMeasure γbar ∧
      γbar M.graphᶜ = 0 ∧ TendstoWeakly (fun n => γ (φ n)) γbar ∧
      ∃ μbar : StationaryPolicy M, γbar = (γbar.map Prod.fst) ⊗ₘ μbar.kernel := by sorry

end AvgCostLP
