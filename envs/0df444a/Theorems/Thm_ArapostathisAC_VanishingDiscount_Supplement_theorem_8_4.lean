-- Prove2me | Theorems.Thm_ArapostathisAC_VanishingDiscount_Supplement_theorem_8_4
-- name    : ArapostathisAC.VanishingDiscount.Supplement.theorem_8_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:17:28.622807+00:00
-- url     : https://prove2.me/theorems/d46bc394-3d3c-4b6c-929f-403c8ac63d59
-- title:
--   Theorem 8.4 (corrected: the converse weights are nonnegative and not all zero) — positive scalarizations give Pareto optima, and every Pareto optimum minimizes a nonnegative scalarization
-- statement:
--   In the model of §8 ($S=\{0,1,2,\dots\}$, common compact metric action space $A$, irreducibility under every $f\in\Pi_{SR}$), let $I_R$ be compact and let $c_1,\dots,c_m\in C_b(S\times A)$, $m\ge1$. Call $f\in\Pi_{SSR}$ Pareto optimal if no $\bar f\in\Pi_{SSR}$ has $\int c_i\,d\hat\eta(\bar f)\le\int c_i\,d\hat\eta(f)$ for all $i$ with strict inequality for some $i$. Then:
--
--   1. any $f\in\Pi_{SSR}$ that minimizes $\sum_{i=1}^m\lambda_i\int c_i\,d\hat\eta(f)$ over $\Pi_{SSR}$ for some $\lambda_i>0$ is Pareto optimal;
--   2. conversely, any Pareto optimal $\bar f\in\Pi_{SSR}$ minimizes $\sum_i\lambda_i\int c_i\,d\hat\eta(\cdot)$ over $\Pi_{SSR}$ for some $\lambda_i\ge0$, not all zero.
--
--   **Formalization Note** Policies enter through their occupation measures $\hat\eta(f)\in I_R$; the integrals are Bochner integrals of bounded continuous functions against probability measures.
--
--   Differences from the source:
--   - encoding: η̂(f) for f ∈ Π_SSR → occ f η built from an invariant probability vector η of f; reason: under the standing irreducibility the invariant probability vector of a stable f is unique
--   - correction: the converse 'minimizes the above functional for some choice of λ_i ≥ 0, 1 ≤ i ≤ m' → some λ_i ≥ 0, not all zero; reason: with λ = 0 every f minimizes, so the printed converse has no content; Remark 8.4 describes the converse as partial only because λ_i ≥ 0 replaces λ_i > 0, and a supporting hyperplane of the convex set of cost vectors at a Pareto point gives a nonzero λ ≥ 0
--   - reading: m costs c_i, 1 ≤ i ≤ m → m ≥ 1; reason: the multiobjective problem has at least one cost; needed for a nonzero weight vector
--   - reading: 'Let I_R be compact' (p. 335) in the §8 model → compactness of I_R is the hypothesis; Assumption 5.20 is not assumed; reason: the multiobjective paragraph replaces the constrained setting's Assumption 5.20 by compactness of I_R, which 5.20 implies
--   - reading: the standing assumptions of §5.3 (p. 309): U(i) replicas of one compact metric A, S the single communicating class under every f ∈ Π_SR → CMP with U(i) = A, A compact metric (with its automatic second countability as an instance), irreducibility under every stationary randomized policy; reason: these are the section's stated standing assumptions
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 335, Theorem 8.4, Pareto optimality and Remark 8.4; p. 333, §8 setting

import Mathlib
import Definitions.Def_ArapostathisAC_VanishingDiscount_CMP
import Definitions.Def_ArapostathisAC_VanishingDiscount_StationaryChain
import Definitions.Def_ArapostathisAC_VanishingDiscount_Supplement_Occupation

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open ArapostathisAC.VanishingDiscount

namespace ArapostathisAC.VanishingDiscount.Supplement

/-- Theorem 8.4 (p. 335), corrected converse. Model of §8 (`S = ℕ`, common compact metric `A`,
irreducibility under every `f ∈ Π_SR`), with `I_R` compact and `m ≥ 1` costs `c_i ∈ C_b(S × A)`.
Any `f ∈ Π_SSR` minimizing `∑_i λ_i ∫ c_i dη̂(f)` over `Π_SSR` for some `λ_i > 0` is Pareto optimal.
Conversely, any Pareto optimal `f̄ ∈ Π_SSR` minimizes this functional for some `λ_i ≥ 0`, not
all zero. -/
theorem theorem_8_4 {A : Type*} [MetricSpace A] [CompactSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (hstd : StandingConvex M)
    (hcpt : IsCompact {μ : ProbabilityMeasure (ℕ × A) | (μ : Measure (ℕ × A)) ∈ occR M})
    (m : ℕ) (hm : 0 < m) (cs : Fin m → ℕ × A → ℝ) (hcs : ∀ i, Continuous (cs i))
    (hcsb : ∀ i, ∃ C, ∀ p, |cs i p| ≤ C) :
    (∀ μ ∈ occR M, ∀ lam : Fin m → ℝ, (∀ i, 0 < lam i) →
      (∀ μ' ∈ occR M, ∑ i, lam i * ∫ p, cs i p ∂μ ≤ ∑ i, lam i * ∫ p, cs i p ∂μ') →
      IsParetoOccupation M cs μ) ∧
    (∀ μ ∈ occR M, IsParetoOccupation M cs μ →
      ∃ lam : Fin m → ℝ, (∀ i, 0 ≤ lam i) ∧ lam ≠ 0 ∧
        ∀ μ' ∈ occR M, ∑ i, lam i * ∫ p, cs i p ∂μ ≤ ∑ i, lam i * ∫ p, cs i p ∂μ') := by sorry

end ArapostathisAC.VanishingDiscount.Supplement
