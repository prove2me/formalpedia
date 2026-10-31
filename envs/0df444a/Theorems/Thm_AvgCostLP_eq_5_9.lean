-- Prove2me | Theorems.Thm_AvgCostLP_eq_5_9
-- name    : AvgCostLP.eq_5_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:31:36.355768+00:00
-- url     : https://prove2.me/theorems/16bf6ebd-74bf-4617-b79f-c52151640335
-- title:
--   (5.9) — $\langle\bar\gamma,c\rangle\le\lim_n\langle\gamma_n,c\rangle=\underline\rho$
-- statement:
--   Let $\mathbb X$ be a Borel space and $\mathbb A$ countable and discrete. Let $\Gamma_j$ satisfy (SU), let $(O_j,D_j,\nu_j)$ satisfy (M) for $K=\mathrm{proj}_{\mathbb X}(\Gamma_j)$, and let $B^1_{j,m,\ell},B^2_{j,\ell}$ be closed sets with the properties of Lemma 5.1. Let $\gamma_n$ be probability measures on $\Gamma$ with $\int(1+c)\,d\gamma_n<\infty$, satisfying (5.7) for every $h\in\hat F_b(\mathbb X)$ and $\langle\gamma_n,c\rangle\to\underline\rho$ (5.8), and converging weakly to a probability measure $\bar\gamma$ on $\Gamma$. Then
--   $$\langle\bar\gamma,c\rangle\le\lim_{n\to\infty}\langle\gamma_n,c\rangle=\underline\rho. \tag{5.9}$$
--
--   This is lower semicontinuity of $\gamma\mapsto\int c\,d\gamma$ along the sequence, obtained without lower semicontinuity of $c$.
--
--   Differences from the source:
--   - generalization: X a Borel space: separable metrizable and homeomorphic to a Borel subset of a Polish space (p.4) → X metrizable and second countable with its Borel σ-algebra; reason: only the clause 'Borel subset of a Polish space' is dropped, so every Borel space of the paper is an instance (under (SU), X is σ-compact and the clause holds anyway)
--   - encoding: Borel measurable stochastic kernels: Borel maps into P(Y) with the weak topology (p.4) → Mathlib Markov kernels (measurable maps into probability measures); reason: the two notions agree on separable metrizable spaces [3, Props. 7.25-7.26]
--   - encoding: Borel measures on Γ → measures on X × A with γ(Γᶜ) = 0; reason: the paper identifies the two (p.9)
--   - encoding: costs c, J and ρ* in [0, +∞], expectations and ∫ c dγ → ℝ≥0∞ with lintegral; real objective values as toReal of finite lintegrals; reason: Lean convention; same instances
--   - encoding: indices j ∈ ℤ₊ of Γ_j → j : ℕ; reason: shift of the index; same sequences
--   - encoding: continuity / convergence in P(X) with the topology of weak convergence → continuity / convergence of ∫ f dμ for every bounded continuous f; reason: the weak topology is the coarsest making these maps continuous; same instances
--   - generalization: the page's choice of (Γ_j, O_j, D_j, ν_j, B¹_{j,m,ℓ}, B²_{j,ℓ}) and the subsequence of Step (iii), under Assumption 2.1 → any such data with the properties of (SU), (M) for K = proj_X(Γ_j) and Lemma 5.1, any sequence of probability measures on Γ with ∫ w dγ_n < ∞, (5.7) on F̂_b(X), (5.8), weakly converging to a probability measure γ̄ on Γ; (G) not assumed; reason: the page's data and sequence have these properties, and the argument uses nothing else, so the statement specializes to the page's
--   - generalization: ρ̲ in (5.8) is the subvalue of (P) → ρ any real number that is the limit of ⟨γ, c⟩ along the sequence; reason: the argument uses only the convergence; the subvalue is such a limit, so the statement specializes to the page's
-- source:
--   Yu, On Linear Programming for Constrained and Unconstrained Average-Cost Markov Decision Processes with Countable Action Spaces and Strictly Unbounded Costs, arXiv:1905.12095v3, (5.9), p.23

import Mathlib
import Definitions.Def_AvgCostLP_Assumption21
import Definitions.Def_AvgCostLP_IsPrimalFeasible
import Definitions.Def_AvgCostLP_IsLusinSets
import Definitions.Def_AvgCostLP_TendstoWeakly
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace AvgCostLP

/-- Yu, On Linear Programming for Constrained and Unconstrained Average-Cost Markov Decision Processes with Countable Action Spaces and Strictly Unbounded Costs, arXiv:1905.12095v3, (5.9), p.23: `⟨γ̄, c⟩ ≤ lim_{n→∞} ⟨γ_n, c⟩ = ρ̲`.

**Formalization Note** `X` is a Borel space, encoded as metrizable, second countable, with its Borel σ-algebra (the clause "homeomorphic to a Borel subset of a Polish space" is dropped); `A` is countable with the discrete topology and its Borel σ-algebra. Measures on `Γ` are measures on `X × A` concentrated on `Γ`; costs and `J` take values in `ℝ≥0∞`. The data of Step (ii) are hypotheses: an (SU) sequence `Γ_j`, majorization data `(O_j, D_j, ν_j)` from (M) for `K = proj_X(Γ_j)`, closed sets `B¹_{j,m,ℓ}`, `B²_{j,ℓ}` with the properties of Lemma 5.1, a sequence `γ_n` of probability measures on `Γ` with (5.7) on `F̂_b(X)` and (5.8), and its weak limit `γ̄` on `Γ` (Step (iii), same notation for the subsequence). The cost `c` is not assumed lower
semicontinuous. -/
theorem eq_5_9 {X A : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
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
    (hconv : TendstoWeakly γ γbar) :
    ∫⁻ p, M.c p ∂γbar ≤ ENNReal.ofReal ρ := by sorry

end AvgCostLP
