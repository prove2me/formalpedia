-- Prove2me | Theorems.Thm_ExactParallelSampling_QuasiUniform_lemma_4_5
-- name    : ExactParallelSampling.QuasiUniform.lemma_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:51:44.331231+00:00
-- url     : https://prove2.me/theorems/f22805a2-3af9-4712-ac08-84006de6abf7
-- title:
--   Lemma 4.5 — expected and failure-free rounds of Sample: max{T(m,D), T̄(m,D)} ≤ R(C₁K)^D(m^{1/3}log^{(2D−1)/3}n + log^{2D+1}n)
-- statement:
--   Let $\lambda$ be a level function for $\mu$, and assume $\log^3n\ge n_0$, where $n$ is the number of coordinates of $\mu$. Suppose that every run of Iterate on $m'>\log^3n$ coordinates, whatever its random choices, uses at most $KRm'^{1/3}/\log^{2/3}m'$ rounds, for some $K,R\ge1$.
--
--   For $m\le n$ and $D\ge0$, define:
--   - $T(m,D)$: the supremum, over the conditional laws $\nu$ of marginals of $\mu$ on at most $m$ coordinates with $D_\lambda(\nu)\le D$, of the expected number of rounds of Sample$(\nu)$;
--   - $\bar T(m,D)$: the supremum, over the same $\nu$ and over all runs of Sample$(\nu)$ in which no run of Iterate returns "fail", of the number of rounds of the run.
--
--   Then $T(m,0)=\bar T(m,0)=1$ and, for $D\ge1$,
--   $$\max\{T(m,D),\bar T(m,D)\}\le R\,(C_1K)^D\big(m^{1/3}\log^{(2D-1)/3}n+\log^{2D+1}n\big)$$
--   for an absolute constant $C_1$.
--
--   Sample is run with $\gamma\in(0,1]$, $n_0=n_0(\gamma)\ge2^{34/\gamma}$, a Rec round cost $\rho$, and an Iterate with the guarantees of Theorem 6.1 on at least $n_0$ elements.
--
--   The inverse-CDF implementation returns a supported value even at tape endpoint 1. The iteration interface also requires every recovery call to lie in the domain of (A2).
--
--   Differences from the source:
--   - generalization: Algorithm 1 runs Iterate, the algorithm of Theorem 6.1, with threshold n₀(γ) ≥ 2^{34/γ} → Sample is parameterized by any iteration algorithm satisfying IterGuarantee It ρ n₀ (the output guarantees of Theorem 6.1 for ground sets of ≥ n₀ elements), with (2:ℝ)^(34/γ) ≤ n₀; reason: §4 uses Iterate only through the guarantees of Theorem 6.1 (p. 20); the paper's Iterate satisfies them by Theorem 6.1, so the statement specializes to the source's
--   - encoding: Algorithm 1 run against the derived oracles of Lemma 2.1, with circuits recovered by Lemma 7.2 → sampleAux: an explicit recursion on (A, K, y) for the law of X_A given X_K = y. Independence queries are answered by IsCondIndep (Lemma 4.1). Rec is answered by the exact circuit families, charged ρ rounds per phase. Rounds are 1 for line 1, plus one per chain-rule coordinate, plus Iterate's rounds, plus the rounds of the sequential recursive calls. Randomness comes from disjoint sub-tapes, and computed distributions are sampled by the inverse distribution function; reason: this is the round accounting of p. 22–23 and the exact sampling of §2.1; by Lemma 7.2 moment recovery returns exactly these circuit families within ρ = R_q rounds
--   - encoding: Σ^E with E = [n] (any finite coordinate set) and alphabets Σ_j ⊆ [q] → finite linearly ordered types E and α with α nonempty; reason: relabelling; the orders fix the chain-rule order, "the smallest element" of a support and the inverse-distribution draws, none of which the source constrains
--   - encoding: a distribution μ on Σ^E = ∏_{j∈E} Σ_j → a mass function p : (E → α) → ℝ with IsDist p, on a finite alphabet α containing every Σ_j; reason: assignments outside ∏ Σ_j get mass 0, which changes no probability, support, conditional law or independent set
--   - encoding: every run of Iterate on m′ > log³ n coordinates uses at most K R m′^{1/3}/log^{2/3} m′ rounds → for every m′ > log³ n, every independence system with (A1) on Fin m′, every correct Rec and every tape, iterRounds (It m′ ρ) ≤ that bound; reason: these are all the inputs on which Sample runs Iterate (I(ν) on E′ satisfies (A1) by Lemma 2.8(b))
--   - encoding: conditional laws ν of marginals of μ on at most m coordinates; T(m, D) and T̄(m, D) → triples (A, K, y) with A ∩ K = ∅, Pr[X_K = y] > 0, |A| ≤ m and condLevel ≤ D; Texp, Tbar as suprema in [0, ∞]; reason: the law of X_A given X_K = y is exactly a conditional law of the marginal on A ∪ K
--   - encoding: for an absolute constant C₁ → ∃ C₁ > 0 quantified before γ, n₀, ρ, Iterate, μ, λ, K, R and m; reason: absolute constant placement
--   - encoding: Sampling from a computed distribution in Algorithm 1 → inverse-CDF draws choose the greatest positive-mass value at the endpoint u=1; IterGuarantee also requires (A2)-valid recovery calls; reason: endpoint choices do not change the distribution, but must stay in the support for the all-run supremum in Lemma 4.5; the paper invokes Rec only on shortest dependent prefixes
-- source:
--   Shen, Li, Shi and Li (2026), Exact Parallel Sampling without Maximal Independent Sets, supplied PDF, Lemma 4.5, p. 23; SHA256 34a681c96bb71642376464cc79acf05535f33206b14e5949999f5f31c28082d4

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_IsIndepSystem
import Definitions.Def_ExactParallelSampling_QuasiUniform_Distributions
import Definitions.Def_ExactParallelSampling_QuasiUniform_Protocol
import Definitions.Def_ExactParallelSampling_QuasiUniform_Sampler

noncomputable section
open Classical MeasureTheory

namespace ExactParallelSampling.QuasiUniform

/-- **Lemma 4.5 (Rounds)**, Shen, Li, Shi and Li (2026), p. 23. Let `λ` be a level function for
`μ`, and assume `log³ n ≥ n₀`. Suppose that every run of Iterate on `m' > log³ n` coordinates,
whatever its random choices, uses at most `K R m'^{1/3}/log^{2/3} m'` rounds, for some `K, R ≥ 1`.
For `m ≤ n` and `D ≥ 0`, let `T(m, D)` be the supremum, over the conditional laws `ν` of marginals of
`μ` on at most `m` coordinates with `D_λ(ν) ≤ D`, of the expected number of rounds of `Sample(ν)`,
and let `T̄(m, D)` be the supremum, over the same `ν` and over all runs of `Sample(ν)` in which no
run of Iterate returns "fail", of the number of rounds of the run. Then `T(m, 0) = T̄(m, 0) = 1`
and, for `D ≥ 1`,
`max{T(m, D), T̄(m, D)} ≤ R (C₁K)^D (m^{1/3} log^{(2D−1)/3} n + log^{2D+1} n)`
for an absolute constant `C₁`. (Sample is run with `γ ∈ (0, 1]`, `n₀ = n₀(γ) ≥ 2^{34/γ}` and an
Iterate with the guarantees of Theorem 6.1 on at least `n₀` elements, `Rec` costing `ρ` rounds.) -/
theorem lemma_4_5 : ∃ C1 : ℝ, 0 < C1 ∧
    ∀ (γ : ℝ), 0 < γ → γ ≤ 1 → ∀ (n0 ρ : ℕ), (2 : ℝ) ^ (34 / γ) ≤ n0 →
    ∀ It : IterAlgorithm, IterGuarantee It ρ n0 →
    ∀ {E α : Type} [Fintype E] [LinearOrder E] [Fintype α] [LinearOrder α] [Nonempty α]
      (p : (E → α) → ℝ), IsQuasiUniform p →
    ∀ lam : ℕ → ℕ, IsLevelFunction p lam →
    (n0 : ℝ) ≤ Real.logb 2 (Fintype.card E) ^ 3 →
    ∀ K R : ℝ, 1 ≤ K → 1 ≤ R →
    (∀ m' : ℕ, Real.logb 2 (Fintype.card E) ^ 3 < m' →
      ∀ I : Finset (Fin m') → Prop, SubsamplingSM.Offline.IsIndepSystem I → (∀ x, I {x}) →
      ∀ recAns, IsCircuitRecovery I recAns → ∀ ω : Tape,
        ((iterRounds (It m' ρ) ρ (indepOracle I recAns) ω : ℕ∞) : ENNReal) ≤
          ENNReal.ofReal (K * R * (m' : ℝ) ^ (1 / 3 : ℝ) / Real.logb 2 m' ^ (2 / 3 : ℝ))) →
    ∀ m : ℕ, m ≤ Fintype.card E →
      (Texp p It ρ n0 lam m 0 = 1 ∧ Tbar p It ρ n0 lam m 0 = 1) ∧
      ∀ D : ℕ, 1 ≤ D →
        max (Texp p It ρ n0 lam m D) (Tbar p It ρ n0 lam m D) ≤
          ENNReal.ofReal (R * (C1 * K) ^ D *
            ((m : ℝ) ^ (1 / 3 : ℝ) * Real.logb 2 (Fintype.card E) ^ ((2 * (D : ℝ) - 1) / 3) +
              Real.logb 2 (Fintype.card E) ^ (2 * D + 1))) := by sorry

end ExactParallelSampling.QuasiUniform
