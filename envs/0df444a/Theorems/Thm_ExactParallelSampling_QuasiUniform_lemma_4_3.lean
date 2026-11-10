-- Prove2me | Theorems.Thm_ExactParallelSampling_QuasiUniform_lemma_4_3
-- name    : ExactParallelSampling.QuasiUniform.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:52:37.94482+00:00
-- url     : https://prove2.me/theorems/d888543e-982b-434f-b835-fff4d2ac1cdb
-- title:
--   Lemma 4.3 — Sample terminates with probability 1 and its output has law ν
-- statement:
--   For every quasi-uniform $\nu$, Sample$(\nu)$ terminates with probability $1$ and its output is distributed according to $\nu$.
--
--   Algorithm 1 is run with a parameter $\gamma\in(0,1]$, the threshold $n_0=n_0(\gamma)\ge2^{34/\gamma}$, a $\mathrm{Rec}$ round cost $\rho$ and an iteration procedure `It`. The procedure only has to satisfy the guarantees of Theorem 6.1 on ground sets of at least $n_0$ elements: §4 uses Iterate only through them. In the Lean, the run has finitely many rounds and an output with probability $1$, and $\Pr[\text{output}=x]=\nu(x)$ for every $x$.
--
--   The inverse-CDF implementation returns a supported value even at tape endpoint 1. The iteration interface also requires every recovery call to lie in the domain of (A2).
--
--   Differences from the source:
--   - generalization: Algorithm 1 runs Iterate, the algorithm of Theorem 6.1, with threshold n₀(γ) ≥ 2^{34/γ} → Sample is parameterized by any iteration algorithm satisfying IterGuarantee It ρ n₀ (the output guarantees of Theorem 6.1 for ground sets of ≥ n₀ elements), with (2:ℝ)^(34/γ) ≤ n₀; reason: §4 uses Iterate only through the guarantees of Theorem 6.1 (p. 20); the paper's Iterate satisfies them by Theorem 6.1, so the statement specializes to the source's
--   - encoding: Algorithm 1 run against the derived oracles of Lemma 2.1, with circuits recovered by Lemma 7.2 → sampleAux: an explicit recursion on (A, K, y) for the law of X_A given X_K = y. Independence queries are answered by IsCondIndep (Lemma 4.1). Rec is answered by the exact circuit families, charged ρ rounds per phase. Rounds are 1 for line 1, plus one per chain-rule coordinate, plus Iterate's rounds, plus the rounds of the sequential recursive calls. Randomness comes from disjoint sub-tapes, and computed distributions are sampled by the inverse distribution function; reason: this is the round accounting of p. 22–23 and the exact sampling of §2.1; by Lemma 7.2 moment recovery returns exactly these circuit families within ρ = R_q rounds
--   - encoding: Σ^E with E = [n] (any finite coordinate set) and alphabets Σ_j ⊆ [q] → finite linearly ordered types E and α with α nonempty; reason: relabelling; the orders fix the chain-rule order, "the smallest element" of a support and the inverse-distribution draws, none of which the source constrains
--   - encoding: a distribution μ on Σ^E = ∏_{j∈E} Σ_j → a mass function p : (E → α) → ℝ with IsDist p, on a finite alphabet α containing every Σ_j; reason: assignments outside ∏ Σ_j get mass 0, which changes no probability, support, conditional law or independent set
--   - encoding: Sample terminates → the number of rounds is finite and there is an output (out ≠ none), each with probability 1; reason: a call without output is exactly a non-terminating one (or one whose fuel ran out, impossible when calls shrink)
--   - encoding: Sampling from a computed distribution in Algorithm 1 → inverse-CDF draws choose the greatest positive-mass value at the endpoint u=1; IterGuarantee also requires (A2)-valid recovery calls; reason: endpoint choices do not change the distribution, but must stay in the support for the all-run supremum in Lemma 4.5; the paper invokes Rec only on shortest dependent prefixes
-- source:
--   Shen, Li, Shi and Li (2026), Exact Parallel Sampling without Maximal Independent Sets, supplied PDF, Lemma 4.3, p. 21; SHA256 34a681c96bb71642376464cc79acf05535f33206b14e5949999f5f31c28082d4

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_IsIndepSystem
import Definitions.Def_ExactParallelSampling_QuasiUniform_Distributions
import Definitions.Def_ExactParallelSampling_QuasiUniform_Protocol
import Definitions.Def_ExactParallelSampling_QuasiUniform_Sampler

noncomputable section
open Classical MeasureTheory

namespace ExactParallelSampling.QuasiUniform

/-- **Lemma 4.3 (Exactness)**, Shen, Li, Shi and Li (2026), p. 21. For every quasi-uniform `ν`,
`Sample(ν)` terminates with probability 1 and its output is distributed according to `ν`.
Algorithm 1 is run with the parameter `γ ∈ (0, 1]` and threshold `n₀ = n₀(γ) ≥ 2^{34/γ}`, and with
any iteration procedure that has the guarantees of Theorem 6.1 on ground sets of at least `n₀`
elements (Section 4 uses Iterate only through them). -/
theorem lemma_4_3 (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (n0 ρ : ℕ) (hn0 : (2 : ℝ) ^ (34 / γ) ≤ n0)
    (It : IterAlgorithm) (hIt : IterGuarantee It ρ n0)
    {E α : Type} [Fintype E] [LinearOrder E] [Fintype α] [LinearOrder α] [Nonempty α]
    (p : (E → α) → ℝ) (hp : IsQuasiUniform p) :
    tapeLaw {ω | (sample p It ρ n0 ω).rounds = ⊤} = 0 ∧
    tapeLaw {ω | (sample p It ρ n0 ω).out = none} = 0 ∧
    ∀ x : E → α, tapeLaw {ω | (sample p It ρ n0 ω).out = some x} = ENNReal.ofReal (p x) := by sorry

end ExactParallelSampling.QuasiUniform
