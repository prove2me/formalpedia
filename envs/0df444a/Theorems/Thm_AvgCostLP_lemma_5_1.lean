-- Prove2me | Theorems.Thm_AvgCostLP_lemma_5_1
-- name    : AvgCostLP.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:28:33.264991+00:00
-- url     : https://prove2.me/theorems/62246379-39c6-4dc0-91d0-57592f5069c0
-- title:
--   Lemma 5.1 — Lusin sets $B^1_{j,m,\ell}$, $B^2_{j,\ell}$ for $c^m$ and $q$
-- statement:
--   Let $\mathbb X$ be a Borel space and $\mathbb A$ countable and discrete. Let $\nu$ be a finite Borel measure on $\mathbb X$ and $F\subset\mathbb A$ a finite set (in the paper, $\nu=\nu_j$ from (M) for $K=\mathrm{proj}_{\mathbb X}(\Gamma_j)$ and $F=F_j=\mathrm{proj}_{\mathbb A}(\Gamma_j)$). For each $\ell\in\mathbb Z_+$ there is a closed set $B^2_\ell\subset\mathbb X$ and, for each $m\in\mathbb Z_+$, a closed set $B^1_{m,\ell}\subset\mathbb X$ such that
--
--   1. $\nu(\mathbb X\setminus B^1_{m,\ell})\le\ell^{-1}$ and $\nu(\mathbb X\setminus B^2_\ell)\le\ell^{-1}$;
--   2. restricted to $B^1_{m,\ell}\times F$ the truncated cost $c^m(\cdot)=\min\{c(\cdot),m\}$ is continuous, and restricted to $B^2_\ell\times F$ the state transition kernel $q(dy\mid\cdot,\cdot)$ is continuous.
--
--   These closed sets carry the continuity that the model lacks; together with the majorizing measures they control the discontinuities in Steps (ii)–(iv).
--
--   Differences from the source:
--   - generalization: X a Borel space: separable metrizable and homeomorphic to a Borel subset of a Polish space (p.4) → X metrizable and second countable with its Borel σ-algebra; reason: only the clause 'Borel subset of a Polish space' is dropped, so every Borel space of the paper is an instance (under (SU), X is σ-compact and the clause holds anyway)
--   - encoding: Borel measurable stochastic kernels: Borel maps into P(Y) with the weak topology (p.4) → Mathlib Markov kernels (measurable maps into probability measures); reason: the two notions agree on separable metrizable spaces [3, Props. 7.25-7.26]
--   - encoding: Borel measures on Γ → measures on X × A with γ(Γᶜ) = 0; reason: the paper identifies the two (p.9)
--   - encoding: costs c, J and ρ* in [0, +∞], expectations and ∫ c dγ → ℝ≥0∞ with lintegral; real objective values as toReal of finite lintegrals; reason: Lean convention; same instances
--   - encoding: continuity / convergence in P(X) with the topology of weak convergence → continuity / convergence of ∫ f dμ for every bounded continuous f; reason: the weak topology is the coarsest making these maps continuous; same instances
--   - generalization: ν_j from (M) for K = proj_X(Γ_j) and F_j = proj_A(Γ_j) → any finite Borel measure ν on X and any finite set F ⊂ A; reason: ν_j is finite and F_j is finite (Γ_j compact, A discrete), so the statement specializes to the paper's for each j
--   - encoding: j, m, ℓ ∈ ℤ₊ and ℓ⁻¹ → m, ℓ : ℕ with 1 ≤ m, 1 ≤ ℓ, and (ℓ : ℝ≥0∞)⁻¹; reason: same indices; ℓ ≥ 1 keeps ℓ⁻¹ finite
-- source:
--   Yu, On Linear Programming for Constrained and Unconstrained Average-Cost Markov Decision Processes with Countable Action Spaces and Strictly Unbounded Costs, arXiv:1905.12095v3, Lemma 5.1, p.21

import Mathlib
import Definitions.Def_AvgCostLP_Model
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace AvgCostLP

/-- Yu, On Linear Programming for Constrained and Unconstrained Average-Cost Markov Decision Processes with Countable Action Spaces and Strictly Unbounded Costs, arXiv:1905.12095v3, Lemma 5.1, p.21: for each `j, m ∈ ℤ₊` and `ℓ ∈ ℤ₊` there exist closed subsets
`B¹_{j,m,ℓ}` and `B²_{j,ℓ}` of `X` such that
(i) `ν_j(X \ B¹_{j,m,ℓ}) ≤ ℓ⁻¹` and `ν_j(X \ B²_{j,ℓ}) ≤ ℓ⁻¹`;
(ii) restricted to `B¹_{j,m,ℓ} × F_j` the function `c^m = min{c, m}` is continuous, and
restricted to `B²_{j,ℓ} × F_j` the kernel `q(dy | ·, ·)` is continuous.

In Lean, for any finite measure `ν` on `X` and any finite set `F ⊂ A` (the paper's `ν_j` and
`F_j = proj_A(Γ_j)`): for each `ℓ ≥ 1` there is `B²` (independent of `m`) and, for each `m ≥ 1`,
a `B¹`, with these properties.

**Formalization Note** `X` is a Borel space, encoded as metrizable, second countable, with its Borel σ-algebra (the clause "homeomorphic to a Borel subset of a Polish space" is dropped); `A` is countable with the discrete topology and its Borel σ-algebra. Measures on `Γ` are measures on `X × A` concentrated on `Γ`; costs and `J` take values in `ℝ≥0∞`. Continuity of `q` into `P(X)` (weak topology) is continuity
of `(x, a) ↦ ∫ f dq(· | x, a)` for every bounded continuous `f`. -/
theorem lemma_5_1 {X A : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A] [Countable A]
    (M : Model X A)
    (ν : Measure X) [IsFiniteMeasure ν] (F : Set A) (hF : F.Finite) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ∃ B2 : Set X, IsClosed B2 ∧ ν B2ᶜ ≤ (ℓ : ℝ≥0∞)⁻¹ ∧
      (∀ f : X →ᵇ ℝ, ContinuousOn (fun p : X × A => ∫ y, f y ∂(M.q p)) (B2 ×ˢ F)) ∧
      ∀ m : ℕ, 1 ≤ m → ∃ B1 : Set X, IsClosed B1 ∧ ν B1ᶜ ≤ (ℓ : ℝ≥0∞)⁻¹ ∧
        ContinuousOn (fun p : X × A => min (M.c p) (m : ℝ≥0∞)) (B1 ×ˢ F) := by sorry

end AvgCostLP
