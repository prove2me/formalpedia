-- Prove2me | Theorems.Thm_AvgCostLP_lemma_5_4
-- name    : AvgCostLP.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:31:23.370977+00:00
-- url     : https://prove2.me/theorems/568ddc8d-c62f-4a78-aaea-d99c1248bac6
-- title:
--   Lemma 5.4 — $(\bar\mu,\bar p)$ is a stationary pair with $J(\bar\mu,\bar p)=\langle\bar\gamma,c\rangle\le\underline\rho$
-- statement:
--   Under the hypotheses of (5.9), assume moreover that $\hat C_b(\mathbb X)$ is a family of bounded continuous functions that determines probability measures on $\mathbb X$ (5.5), that (5.7) also holds for every $h\in\hat C_b(\mathbb X)$, and that $\bar\gamma(d(x,a))=\bar\mu(da\mid x)\,\bar p(dx)$ with $\bar p$ the marginal of $\bar\gamma$ and $\bar\mu$ a stationary policy. Then the pair $(\bar\mu,\bar p)$ is a stationary pair with
--   $$J(\bar\mu,\bar p)=\langle\bar\gamma,c\rangle\le\underline\rho .$$
--
--   With $\bar r=\underline\rho-\langle\bar\gamma,c\rangle\ge0$ this gives $((1,0),\underline\rho)=(L\bar\gamma,\langle\bar\gamma,c\rangle+\bar r)\in H$, which closes the proof of Theorem 3.1.
--
--   Differences from the source:
--   - generalization: X a Borel space: separable metrizable and homeomorphic to a Borel subset of a Polish space (p.4) → X metrizable and second countable with its Borel σ-algebra; reason: only the clause 'Borel subset of a Polish space' is dropped, so every Borel space of the paper is an instance (under (SU), X is σ-compact and the clause holds anyway)
--   - encoding: Borel measurable stochastic kernels: Borel maps into P(Y) with the weak topology (p.4) → Mathlib Markov kernels (measurable maps into probability measures); reason: the two notions agree on separable metrizable spaces [3, Props. 7.25-7.26]
--   - encoding: Borel measures on Γ → measures on X × A with γ(Γᶜ) = 0; reason: the paper identifies the two (p.9)
--   - encoding: costs c, J and ρ* in [0, +∞], expectations and ∫ c dγ → ℝ≥0∞ with lintegral; real objective values as toReal of finite lintegrals; reason: Lean convention; same instances
--   - encoding: indices j ∈ ℤ₊ of Γ_j → j : ℕ; reason: shift of the index; same sequences
--   - encoding: continuity / convergence in P(X) with the topology of weak convergence → continuity / convergence of ∫ f dμ for every bounded continuous f; reason: the weak topology is the coarsest making these maps continuous; same instances
--   - generalization: the page's choice of (Γ_j, O_j, D_j, ν_j, B¹_{j,m,ℓ}, B²_{j,ℓ}) and the subsequence of Step (iii), under Assumption 2.1 → any such data with the properties of (SU), (M) for K = proj_X(Γ_j) and Lemma 5.1, any sequence of probability measures on Γ with ∫ w dγ_n < ∞, (5.7) on F̂_b(X), (5.8), weakly converging to a probability measure γ̄ on Γ; (G) not assumed; reason: the page's data and sequence have these properties, and the argument uses nothing else, so the statement specializes to the page's
--   - generalization: Ĉ_b(X) a countable subset of C_b(X) that determines weak convergence → any family of bounded continuous functions with the separation property (5.5); reason: the paper's Ĉ_b(X) has (5.5); countability and convergence-determination are not used in this step
--   - generalization: ρ̲ in (5.8) is the subvalue of (P) → ρ any real number that is the limit of ⟨γ, c⟩ along the sequence; reason: the argument uses only the convergence; the subvalue is such a limit, so the statement specializes to the page's
--   - generalization: (μ̄, p̄) the decomposition chosen in Step (iii) → any stationary policy μ̄ with γ̄ = μ̄ ⊗ p̄, where p̄ is the marginal of γ̄; reason: the page's decomposition is one of these, and the argument uses nothing else about it
-- source:
--   Yu, On Linear Programming for Constrained and Unconstrained Average-Cost Markov Decision Processes with Countable Action Spaces and Strictly Unbounded Costs, arXiv:1905.12095v3, Lemma 5.4, p.23 (with (5.5), p.21)

import Mathlib
import Definitions.Def_AvgCostLP_Assumption21
import Definitions.Def_AvgCostLP_IsPrimalFeasible
import Definitions.Def_AvgCostLP_IsLusinSets
import Definitions.Def_AvgCostLP_TendstoWeakly
import Definitions.Def_AvgCostLP_IsStationaryPair
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace AvgCostLP

/-- Yu, On Linear Programming for Constrained and Unconstrained Average-Cost Markov Decision Processes with Countable Action Spaces and Strictly Unbounded Costs, arXiv:1905.12095v3, Lemma 5.4, p.23: the pair `(μ̄, p̄)` is a stationary pair with
`J(μ̄, p̄) = ⟨γ̄, c⟩ ≤ ρ̲`.

**Formalization Note** `X` is a Borel space, encoded as metrizable, second countable, with its Borel σ-algebra (the clause "homeomorphic to a Borel subset of a Polish space" is dropped); `A` is countable with the discrete topology and its Borel σ-algebra. Measures on `Γ` are measures on `X × A` concentrated on `Γ`; costs and `J` take values in `ℝ≥0∞`. The data of Step (ii) are hypotheses: an (SU) sequence `Γ_j`, majorization data `(O_j, D_j, ν_j)` from (M) for `K = proj_X(Γ_j)`, closed sets `B¹_{j,m,ℓ}`, `B²_{j,ℓ}` with the properties of Lemma 5.1, a sequence `γ_n` of probability measures on `Γ` with (5.7) on `F̂_b(X)` and (5.8), and its weak limit `γ̄` on `Γ` (Step (iii), same notation for the subsequence). In addition, `Ĉ_b(X)` is a family of bounded
continuous functions that determines probability measures on `X` (5.5), (5.7) holds on it too,
and `γ̄ = μ̄ ⊗ p̄` with `p̄ = γ̂̄` is the decomposition of Step (iii). -/
theorem lemma_5_4 {X A : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A] [Countable A]
    (M : Model X A)
    (Γs : ℕ → Set (X × A)) (hSU : IsSUSeq M Γs)
    (O D : ℕ → Set X) (ν : ℕ → Measure X)
    (hMaj : ∀ j, IsMajorizing M (Prod.fst '' Γs j) (O j) (D j) (ν j))
    (B1 : ℕ → ℕ → ℕ → Set X) (B2 : ℕ → ℕ → Set X) (hLusin : IsLusinSets M Γs ν B1 B2)
    (γ : ℕ → Measure (X × A)) (ρ : ℝ)
    (hγ : ∀ n, IsProbabilityMeasure (γ n) ∧ γ n M.graphᶜ = 0 ∧ ∫⁻ p, (1 + M.c p) ∂(γ n) < ⊤)
    (h57 : ∀ h ∈ testIndicators O D B1 B2, Tendsto (fun n => residual M (γ n) h) atTop (𝓝 0))
    (h58 : Tendsto (fun n => (∫⁻ p, M.c p ∂(γ n)).toReal) atTop (𝓝 ρ))
    (γbar : Measure (X × A)) [IsProbabilityMeasure γbar] (hγbar : γbar M.graphᶜ = 0)
    (hconv : TendstoWeakly γ γbar)
    (Chat : Set (X →ᵇ ℝ))
    (hsep : ∀ p p' : ProbabilityMeasure X,
      (∀ h ∈ Chat, ∫ x, h x ∂(p : Measure X) = ∫ x, h x ∂(p' : Measure X)) → p = p')
    (h57C : ∀ h ∈ Chat, Tendsto (fun n => residual M (γ n) h) atTop (𝓝 0))
    (μbar : StationaryPolicy M) (pbar : ProbabilityMeasure X)
    (hpbar : (pbar : Measure X) = γbar.map Prod.fst)
    (hdec : γbar = (pbar : Measure X) ⊗ₘ μbar.kernel) :
    IsStationaryPair M μbar pbar ∧ avgCost M μbar.toPolicy pbar = ∫⁻ p, M.c p ∂γbar ∧
      ∫⁻ p, M.c p ∂γbar ≤ ENNReal.ofReal ρ := by sorry

end AvgCostLP
