-- Prove2me | Theorems.Thm_ExactParallelSampling_QuasiUniform_theorem_7_1
-- name    : ExactParallelSampling.QuasiUniform.theorem_7_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:51:07.016644+00:00
-- url     : https://prove2.me/theorems/91fc358f-381e-411e-838b-32dec01bb7ac
-- title:
--   Theorem 7.1 — main theorem, full form: for every γ ∈ (0,1], exact sampling in O(R_q C_γ^q(n^{1/3}log^{(2q−3)/3}n + log^{2q−1}n)) rounds with 2^{O(q)}n^{6+γ} queries per round
-- statement:
--   For every $\gamma\in(0,1]$ there is an algorithm with the following properties.
--   - **Exactness.** For every $q\ge2$, given the counting oracle of any quasi-uniform distribution $\mu$ on $[q]^n$, it outputs a sample distributed exactly according to $\mu$.
--   - **Rounds.** In expectation, and also with probability $1-n^{-\omega(1)}$, it uses $O(R_qC_\gamma^q(n^{1/3}\log^{(2q-3)/3}n+\log^{2q-1}n))$ rounds, where $R_q=O(\log q)$ and $C_\gamma=O(\gamma^{-1/3})$.
--   - **Queries.** It uses $2^{O(q)}n^{6+\gamma}$ counting queries per round.
--
--   Every constant hidden in the theorem depends only on $\gamma$, and $q$ enters only through the stated terms. Here $R_q=2+\lceil\log_2\log_2L_q\rceil$ and $L_q=\mathrm{lcm}(1,\dots,q)$ (p. 37). Logarithms are base 2.
--
--   In the Lean, with constants depending only on $\gamma$ and with $K_c$, $K_r$ absolute:
--   - $C_\gamma\le K_c\gamma^{-1/3}$ and $R_q\le K_r\log_2q$;
--   - for all $n\ge n_*$, all $q\ge2$ and all quasi-uniform $\mu$: $\mathbb E[T]\le A\,R_qC_\gamma^q(\dots)$, every batch of every run has at most $2^{Bq}n^{6+\gamma}$ queries, and for every $c>0$, eventually in $n$, $\Pr[T>A\,R_qC_\gamma^q(\dots)]\le n^{-c}$;
--   - exactness holds for every $n$.
--
--   Differences from the source:
--   - encoding: an algorithm that, given the counting oracle of μ on [q]^n (and n, q), outputs a sample → a CountAlgorithm: for every n, q a Protocol whose next batch or output is a measurable function of the transcript (earlier batches and exact real answers) and of a tape of independent uniform [0, 1] numbers; reason: this is the model of §2.1: rounds of query batches chosen from earlier answers and private randomness, free exact computation, exact sampling from computed distributions
--   - encoding: samples exactly: terminates with probability 1 and the output is distributed according to μ → SamplesExactly: tapeLaw {rounds = ⊤} = 0 and tapeLaw {output = some x} = μ(x) for every x, for every n and every q ≥ 2; reason: definition of §2.1; exactness is claimed for every n, the resource bounds only asymptotically
--   - reading: O(R_q C^q (n^{1/3} log^{(2q−3)/3} n + log^{2q−1} n)) rounds in expectation, with R_q = O(log q) → E[T] ≤ A · R_q · C^q · (…) for all n ≥ n* and q ≥ 2, with R_q = 2 + ⌈log₂ log₂ lcm(1,…,q)⌉ as defined on p. 37, plus the separate clause R_q ≤ K_r log₂ q; reason: the O is asymptotic in n and uniform in q and μ; p. 37 defines R_q explicitly and proves R_q = O(log q)
--   - reading: "and also with probability 1 − n^{−ω(1)}" → for every c > 0 there is n_c such that for all n ≥ n_c, q ≥ 2 and μ, Pr[T > A R_q C^q (…)] ≤ n^{−c}, with the same multiplier A; reason: n^{−ω(1)} is a function of n alone tending to 0 faster than every polynomial (the proof gives 3n·2^{−log³ n/2}); one A serves both bounds after taking the larger of two constants
--   - reading: 2^{O(q)} n^{6+γ} counting queries per round → every batch of every run (every tape) has at most 2^{Bq} n^{6+γ} queries, for n ≥ n*; reason: q ≥ 2 lets a constant factor be absorbed into 2^{Bq}; the bound holds on every run, not only in expectation
--   - reading: C_γ = O(γ^{−1/3}); every hidden constant depends only on γ → ∃ K_c > 0 before γ with C_γ ≤ K_c γ^{−1/3}; A, B, n*, the algorithm chosen after γ; reason: constant placement as the source states it
-- source:
--   Shen, Li, Shi and Li (2026), Exact Parallel Sampling without Maximal Independent Sets, supplied PDF, Theorem 7.1, p. 37; SHA256 34a681c96bb71642376464cc79acf05535f33206b14e5949999f5f31c28082d4

import Mathlib
import Definitions.Def_ExactParallelSampling_QuasiUniform_Distributions
import Definitions.Def_ExactParallelSampling_QuasiUniform_Protocol
import Definitions.Def_ExactParallelSampling_QuasiUniform_EfronStein

noncomputable section
open Classical MeasureTheory

namespace ExactParallelSampling.QuasiUniform

/-- **Theorem 7.1 (Main theorem, full form)**, Shen, Li, Shi and Li (2026), p. 37. For every
`γ ∈ (0, 1]` there is an algorithm that, for every `q ≥ 2`, given the counting oracle of any
quasi-uniform distribution `μ` on `[q]^n`, outputs a sample distributed exactly according to `μ`.
In expectation, and also with probability `1 − n^{−ω(1)}`, it uses
`O(R_q C_γ^q (n^{1/3} log^{(2q−3)/3} n + log^{2q−1} n))` rounds, where `R_q = O(log q)` and
`C_γ = O(γ^{−1/3})`, and it uses `2^{O(q)} n^{6+γ}` counting queries per round. Every hidden
constant depends only on `γ`; `R_q = 2 + ⌈log₂ log₂ lcm(1, …, q)⌉` (p. 37). -/
theorem theorem_7_1 :
    (∃ Kr : ℝ, ∀ q : ℕ, 2 ≤ q → (Rq q : ℝ) ≤ Kr * Real.logb 2 q) ∧
    ∃ Kc : ℝ, 0 < Kc ∧ ∀ γ : ℝ, 0 < γ → γ ≤ 1 →
    ∃ Cγ : ℝ, 0 < Cγ ∧ Cγ ≤ Kc * γ ^ (-(1 / 3 : ℝ)) ∧
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∃ nstar : ℕ, ∃ alg : CountAlgorithm,
    -- exact sampling, for every `n` and `q`
    (∀ n q : ℕ, 2 ≤ q → ∀ p : (Fin n → Fin q) → ℝ, IsQuasiUniform p →
      SamplesExactly (alg n q) p) ∧
    -- expected rounds and queries per round (asymptotic in `n`, uniform in `q` and `μ`)
    (∀ n q : ℕ, nstar ≤ n → 2 ≤ q → ∀ p : (Fin n → Fin q) → ℝ, IsQuasiUniform p →
      expectedRounds (alg n q) p ≤
          ENNReal.ofReal (A * Rq q * Cγ ^ q * ((n : ℝ) ^ (1 / 3 : ℝ) *
            Real.logb 2 n ^ ((2 * (q : ℝ) - 3) / 3) + Real.logb 2 n ^ (2 * q - 1))) ∧
      ∀ (ω : Tape) (r : ℕ), (r : ℕ∞) < (alg n q).rounds (countOracle p) ω →
        (((alg n q).batchAt (countOracle p) ω r).card : ℝ) ≤ (2 : ℝ) ^ (B * q) * (n : ℝ) ^ (6 + γ)) ∧
    -- the same round bound with probability `1 − n^{−ω(1)}`
    (∀ c : ℝ, 0 < c → ∃ nc : ℕ, ∀ n q : ℕ, nc ≤ n → 2 ≤ q →
      ∀ p : (Fin n → Fin q) → ℝ, IsQuasiUniform p →
        tapeLaw {ω | ENNReal.ofReal (A * Rq q * Cγ ^ q * ((n : ℝ) ^ (1 / 3 : ℝ) *
            Real.logb 2 n ^ ((2 * (q : ℝ) - 3) / 3) + Real.logb 2 n ^ (2 * q - 1))) <
          (((alg n q).rounds (countOracle p) ω : ℕ∞) : ENNReal)} ≤
          ENNReal.ofReal ((n : ℝ) ^ (-c))) := by sorry

end ExactParallelSampling.QuasiUniform
