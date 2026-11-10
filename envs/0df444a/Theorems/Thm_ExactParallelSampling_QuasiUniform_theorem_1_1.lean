-- Prove2me | Theorems.Thm_ExactParallelSampling_QuasiUniform_theorem_1_1
-- name    : ExactParallelSampling.QuasiUniform.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:50:57.862181+00:00
-- url     : https://prove2.me/theorems/a23cf76c-a6c0-4d9c-89d3-76ad5b0d389d
-- title:
--   Theorem 1.1 — main theorem: every quasi-uniform distribution on [q]^n is sampled exactly in O(R_q C^q(n^{1/3}log^{(2q−3)/3}n + log^{2q−1}n)) rounds with 2^{O(q)}n^7 queries per round
-- statement:
--   There is an algorithm with the following properties.
--   - **Exactness.** For every $q\ge2$, given the counting oracle of any quasi-uniform distribution $\mu$ on $[q]^n$, it outputs a sample distributed exactly according to $\mu$.
--   - **Rounds.** In expectation, and also with probability $1-n^{-\omega(1)}$, it uses $O(R_qC^q(n^{1/3}\log^{(2q-3)/3}n+\log^{2q-1}n))$ rounds, where $R_q=O(\log q)$ and $C$ is an absolute constant.
--   - **Queries.** It uses $2^{O(q)}n^7$ counting queries per round.
--   - **Constant $q$.** For every constant $q$ it uses $O(n^{1/3}\log^{(2q-3)/3}n)$ rounds and $O(n^7)$ queries per round.
--
--   All constants in the theorem are absolute. Here $R_q=2+\lceil\log_2\log_2\mathrm{lcm}(1,\dots,q)\rceil$ (p. 37), and logarithms are base 2.
--
--   In the Lean, with absolute constants $A,B,C>0$, $n_*$ and $K_r$, and one algorithm for all $n$ and $q$:
--   - $R_q\le K_r\log_2q$;
--   - exactness holds for every $n$;
--   - for all $n\ge n_*$, $q\ge2$ and quasi-uniform $\mu$: $\mathbb E[T]\le A\,R_qC^q(\dots)$ and every batch of every run has at most $2^{Bq}n^7$ queries;
--   - for every $c>0$, eventually in $n$ and uniformly in $q$ and $\mu$, $\Pr[T>A\,R_qC^q(\dots)]\le n^{-c}$;
--   - for each fixed $q$ there are $A_q$ and $n_q$ with $\mathbb E[T]\le A_qn^{1/3}\log^{(2q-3)/3}n$ and at most $A_qn^7$ queries per round for $n\ge n_q$, and the matching $n^{-c}$ tail bound.
--
--   Differences from the source:
--   - encoding: an algorithm that, given the counting oracle of μ on [q]^n (and n, q), outputs a sample → a CountAlgorithm: for every n, q a Protocol whose next batch or output is a measurable function of the transcript (earlier batches and exact real answers) and of a tape of independent uniform [0, 1] numbers; reason: this is the model of §2.1: rounds of query batches chosen from earlier answers and private randomness, free exact computation, exact sampling from computed distributions
--   - encoding: samples exactly: terminates with probability 1 and the output is distributed according to μ → SamplesExactly: tapeLaw {rounds = ⊤} = 0 and tapeLaw {output = some x} = μ(x) for every x, for every n and every q ≥ 2; reason: definition of §2.1; exactness is claimed for every n, the resource bounds only asymptotically
--   - reading: O(R_q C^q (n^{1/3} log^{(2q−3)/3} n + log^{2q−1} n)) rounds in expectation, with R_q = O(log q) → E[T] ≤ A · R_q · C^q · (…) for all n ≥ n* and q ≥ 2, with R_q = 2 + ⌈log₂ log₂ lcm(1,…,q)⌉ as defined on p. 37, plus the separate clause R_q ≤ K_r log₂ q; reason: the O is asymptotic in n and uniform in q and μ; p. 37 defines R_q explicitly and proves R_q = O(log q)
--   - reading: "and also with probability 1 − n^{−ω(1)}" → for every c > 0 there is n_c such that for all n ≥ n_c, q ≥ 2 and μ, Pr[T > A R_q C^q (…)] ≤ n^{−c}, with the same multiplier A; reason: n^{−ω(1)} is a function of n alone tending to 0 faster than every polynomial (the proof gives 3n·2^{−log³ n/2}); one A serves both bounds after taking the larger of two constants
--   - reading: 2^{O(q)} n^{7} counting queries per round → every batch of every run (every tape) has at most 2^{Bq} n^{7} queries, for n ≥ n*; reason: q ≥ 2 lets a constant factor be absorbed into 2^{Bq}; the bound holds on every run, not only in expectation
--   - reading: "In particular, for every constant q it uses O(n^{1/3} log^{(2q−3)/3} n) rounds and O(n^7) queries per round" → a separate conjunct: for each q ≥ 2 there are A_q, n_q bounding E[T], the tail (∀ c > 0, eventually ≤ n^{−c}) and the batch sizes A_q n^7, for the same algorithm; reason: the round bound of the clause is read with the same "in expectation and with probability 1 − n^{−ω(1)}" as the main clause; the constants may depend on q because q is constant there
-- source:
--   Shen, Li, Shi and Li (2026), Exact Parallel Sampling without Maximal Independent Sets, supplied PDF, Theorem 1.1, p. 4; SHA256 34a681c96bb71642376464cc79acf05535f33206b14e5949999f5f31c28082d4

import Mathlib
import Definitions.Def_ExactParallelSampling_QuasiUniform_Distributions
import Definitions.Def_ExactParallelSampling_QuasiUniform_Protocol
import Definitions.Def_ExactParallelSampling_QuasiUniform_EfronStein

noncomputable section
open Classical MeasureTheory

namespace ExactParallelSampling.QuasiUniform

/-- **Theorem 1.1 (Main theorem)**, Shen, Li, Shi and Li (2026), p. 4. There is an algorithm that,
for every `q ≥ 2`, given the counting oracle of any quasi-uniform distribution `μ` on `[q]^n`,
outputs a sample distributed exactly according to `μ`. In expectation, and also with probability
`1 − n^{−ω(1)}`, it uses `O(R_q C^q (n^{1/3} log^{(2q−3)/3} n + log^{2q−1} n))` rounds, where
`R_q = O(log q)` and `C` is an absolute constant, and it uses `2^{O(q)} n^7` counting queries per
round. In particular, for every constant `q` it uses `O(n^{1/3} log^{(2q−3)/3} n)` rounds and
`O(n^7)` queries per round. All constants are absolute; `R_q = 2 + ⌈log₂ log₂ lcm(1, …, q)⌉`
(p. 37). -/
theorem theorem_1_1 :
    (∃ Kr : ℝ, ∀ q : ℕ, 2 ≤ q → (Rq q : ℝ) ≤ Kr * Real.logb 2 q) ∧
    ∃ A B C : ℝ, 0 < A ∧ 0 < B ∧ 0 < C ∧ ∃ nstar : ℕ, ∃ alg : CountAlgorithm,
    -- exact sampling, for every `n` and `q`
    (∀ n q : ℕ, 2 ≤ q → ∀ p : (Fin n → Fin q) → ℝ, IsQuasiUniform p →
      SamplesExactly (alg n q) p) ∧
    -- expected rounds and queries per round (asymptotic in `n`, uniform in `q` and `μ`)
    (∀ n q : ℕ, nstar ≤ n → 2 ≤ q → ∀ p : (Fin n → Fin q) → ℝ, IsQuasiUniform p →
      expectedRounds (alg n q) p ≤
          ENNReal.ofReal (A * Rq q * C ^ q * ((n : ℝ) ^ (1 / 3 : ℝ) *
            Real.logb 2 n ^ ((2 * (q : ℝ) - 3) / 3) + Real.logb 2 n ^ (2 * q - 1))) ∧
      ∀ (ω : Tape) (r : ℕ), (r : ℕ∞) < (alg n q).rounds (countOracle p) ω →
        (((alg n q).batchAt (countOracle p) ω r).card : ℝ) ≤ (2 : ℝ) ^ (B * q) * (n : ℝ) ^ (7 : ℝ)) ∧
    -- the same round bound with probability `1 − n^{−ω(1)}`
    (∀ c : ℝ, 0 < c → ∃ nc : ℕ, ∀ n q : ℕ, nc ≤ n → 2 ≤ q →
      ∀ p : (Fin n → Fin q) → ℝ, IsQuasiUniform p →
        tapeLaw {ω | ENNReal.ofReal (A * Rq q * C ^ q * ((n : ℝ) ^ (1 / 3 : ℝ) *
            Real.logb 2 n ^ ((2 * (q : ℝ) - 3) / 3) + Real.logb 2 n ^ (2 * q - 1))) <
          (((alg n q).rounds (countOracle p) ω : ℕ∞) : ENNReal)} ≤
          ENNReal.ofReal ((n : ℝ) ^ (-c))) ∧
    -- in particular, for every constant `q`
    (∀ q : ℕ, 2 ≤ q → ∃ Aq : ℝ, 0 < Aq ∧ ∃ nq : ℕ,
      (∀ n : ℕ, nq ≤ n → ∀ p : (Fin n → Fin q) → ℝ, IsQuasiUniform p →
        expectedRounds (alg n q) p ≤
            ENNReal.ofReal (Aq * (n : ℝ) ^ (1 / 3 : ℝ) * Real.logb 2 n ^ ((2 * (q : ℝ) - 3) / 3)) ∧
        ∀ (ω : Tape) (r : ℕ), (r : ℕ∞) < (alg n q).rounds (countOracle p) ω →
          (((alg n q).batchAt (countOracle p) ω r).card : ℝ) ≤ Aq * (n : ℝ) ^ (7 : ℝ)) ∧
      ∀ c : ℝ, 0 < c → ∃ nc : ℕ, ∀ n : ℕ, nc ≤ n → ∀ p : (Fin n → Fin q) → ℝ, IsQuasiUniform p →
        tapeLaw {ω | ENNReal.ofReal
            (Aq * (n : ℝ) ^ (1 / 3 : ℝ) * Real.logb 2 n ^ ((2 * (q : ℝ) - 3) / 3)) <
          (((alg n q).rounds (countOracle p) ω : ℕ∞) : ENNReal)} ≤
          ENNReal.ofReal ((n : ℝ) ^ (-c))) := by sorry

end ExactParallelSampling.QuasiUniform
