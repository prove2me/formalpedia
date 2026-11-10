-- Prove2me | Theorems.Thm_ExactParallelSampling_QuasiUniform_theorem_6_1
-- name    : ExactParallelSampling.QuasiUniform.theorem_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:51:56.000752+00:00
-- url     : https://prove2.me/theorems/1c19bda1-bc4c-40f3-a873-43290769ebfd
-- title:
--   Theorem 6.1 — one iteration on any independence system with (A1), (A2): contract, defer with certificates, or fail w.p. ≤ 2^{−n/2}, in (ρ+3)(C₀c_γ^{1/3}n^{1/3}/log^{2/3}n + 1) + 2 rounds
-- statement:
--   Throughout, $I$ is an independence system on a ground set $E$ with $|E|=n$, given by an oracle that answers whether a set $T\subseteq E$ is in $I$. Fix $\gamma\in(0,1]$, write $c_\gamma=48/\gamma$, and assume $n\ge n_0(\gamma)$. Assume:
--   - (A1) every singleton is independent;
--   - (A2) there is a deterministic procedure Rec that, for every $B\in I$ and $x\notin B$ with $B+x\notin I$, computes the family of all circuits contained in $B+x$ in at most $\rho$ rounds. Its queries go to a richer oracle and are counted separately.
--
--   There is a randomized algorithm Iterate that, whatever its random choices, uses at most $(\rho+3)(C_0c_\gamma^{1/3}n^{1/3}/\log^{2/3}n+1)+2$ rounds, for an absolute constant $C_0$, and returns one of the following:
--   - (i) "contract" with a set $U\in I$ of size $|U|\ge n/(5000\log n)$;
--   - (ii) "defer" with a set $R\subseteq E$ of size $|R|\ge2^{-26}n/\log n$ and, for each $x\in R$, a set $T_x\subseteq E\setminus R$ with $T_x\in I$ and $T_x+x\notin I$;
--   - (iii) "fail".
--
--   Every set it returns has been verified by its queries: $U$, and each $T_x$ and $T_x+x$, were asked as independence queries. It returns "fail" with probability at most $2^{-n/2}$. Each round issues $O(n^{5+\gamma}\log n)$ independence queries (at most $K_qn^{5+\gamma}\log n$ for an absolute $K_q$) and the queries of at most $N=\lceil1280n^{4+\gamma}\rceil$ instances of one round of Rec. The algorithm knows $n$, $\rho$ and $\gamma$; it is fixed before $I$ and Rec, and holds for every $\rho$.
--
--   Every recovery query made during execution satisfies all three input conditions of (A2).
--
--   Differences from the source:
--   - encoding: an independence system I on E, |E| = n, with (A1) → Fin n, SubsamplingSM.Offline.IsIndepSystem I and ∀ x, I {x}; reason: the published predicate is the definition of an independence system; any n-element ground set is relabelled as Fin n
--   - encoding: (A2): Rec, a deterministic procedure with at most ρ adaptive rounds of richer-oracle queries, counted separately → a black-box query recover B x answered by any recAns with IsCircuitRecovery I recAns (correct on (A2) inputs, arbitrary elsewhere); a step running Rec instances costs ρ rounds, a step asking independence queries costs 1, a mixed step the larger; the per-round Rec load is the number of instances; reason: Iterate uses Rec only through its output; charging the whole ρ rounds and leaving Rec's answers on other inputs arbitrary only makes the algorithm's task harder
--   - encoding: n ≥ n₀(γ), where n₀(γ) ≥ 2^{34/γ} also exceeds a sufficiently large absolute constant → ∃ n₀ (chosen after γ), ∀ ground sets with n ≥ n₀; reason: the source leaves the threshold unspecified beyond being sufficiently large, so it is an existential threshold depending only on γ
--   - reading: "Each round issues O(n^{5+γ} log n) independence queries" → at most Kq · n^{5+γ} · log₂ n with Kq an absolute constant chosen before γ; reason: the source states C₀ absolute and does not let this O depend on γ; its count R_c N_c Σ|S_j| ≤ ⌈2^{24}n⌉⌈4n^{3+γ} ln(2^{24}n)⌉ n has absolute constants, so the stronger reading is taken
--   - encoding: "Every set it returns has been verified by its queries" → Queried (indep U) for a contraction, and Queried (indep T_x), Queried (indep (T_x + x)) for every certificate; reason: these are the verifying queries named in §6.6 (p. 36)
--   - encoding: "whatever its random choices, uses at most … rounds"; probability of fail → for every tape ω, the run halts and iterRounds ≤ the bound; tapeLaw of the fail event ≤ 2^{−n/2}; reason: random choices are the tape
--   - encoding: (A2) guarantees Rec only when B is independent, x∉B and B+x is dependent → RecoveryCallsValid is a conclusion for every run of Iterate; reason: only these calls can be charged ρ rounds or supplied with the guaranteed circuit family; no behavior outside the domain is assumed
-- source:
--   Shen, Li, Shi and Li (2026), Exact Parallel Sampling without Maximal Independent Sets, supplied PDF, Theorem 6.1, p. 28; SHA256 34a681c96bb71642376464cc79acf05535f33206b14e5949999f5f31c28082d4

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_IsIndepSystem
import Definitions.Def_ExactParallelSampling_QuasiUniform_Distributions
import Definitions.Def_ExactParallelSampling_QuasiUniform_Protocol
import Definitions.Def_ExactParallelSampling_QuasiUniform_IndepSystems

noncomputable section
open Classical MeasureTheory

namespace ExactParallelSampling.QuasiUniform

/-- **Theorem 6.1 (One iteration)**, Shen, Li, Shi and Li (2026), p. 28. Assume (A1) and (A2) for
an independence system `I` on a ground set of `n ≥ n₀(γ)` elements, `γ ∈ (0, 1]`, `c_γ = 48/γ`.
There is a randomized algorithm Iterate that, whatever its random choices, uses at most
`(ρ + 3)(C₀ c_γ^{1/3} n^{1/3}/log^{2/3} n + 1) + 2` rounds, for an absolute constant `C₀`, and
returns one of: (i) "contract" with `U ∈ I`, `|U| ≥ n/(5000 log n)`; (ii) "defer" with `R ⊆ E`,
`|R| ≥ 2^{−26} n/log n` and, for each `x ∈ R`, `T_x ⊆ E ∖ R` with `T_x ∈ I` and `T_x + x ∉ I`;
(iii) "fail". Every set it returns has been verified by its queries, and it returns "fail" with
probability at most `2^{−n/2}`. Each round issues `O(n^{5+γ} log n)` independence queries and the
queries of at most `N = ⌈1280 n^{4+γ}⌉` instances of one round of `Rec`. -/
theorem theorem_6_1 : ∃ C0 : ℝ, 0 < C0 ∧ ∃ Kq : ℝ, 0 < Kq ∧ ∀ γ : ℝ, 0 < γ → γ ≤ 1 →
    ∃ n0 : ℕ, ∃ It : IterAlgorithm, ∀ n : ℕ, n0 ≤ n → ∀ ρ : ℕ,
    ∀ I : Finset (Fin n) → Prop, SubsamplingSM.Offline.IsIndepSystem I → (∀ x, I {x}) →
    ∀ recAns : Finset (Fin n) → Fin n → Finset (Finset (Fin n)), IsCircuitRecovery I recAns →
      (∀ ω : Tape,
        (It n ρ).rounds (indepOracle I recAns) ω ≠ ⊤ ∧
        RecoveryCallsValid (It n ρ) I (indepOracle I recAns) ω ∧
        (∃ k : ℕ, iterRounds (It n ρ) ρ (indepOracle I recAns) ω = (k : ℕ∞) ∧
          (k : ℝ) ≤ ((ρ : ℝ) + 3) * (C0 * cgam γ ^ (1 / 3 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) /
            Real.logb 2 n ^ (2 / 3 : ℝ) + 1) + 2) ∧
        (∀ r : ℕ, (r : ℕ∞) < (It n ρ).rounds (indepOracle I recAns) ω →
          (numIndep ((It n ρ).batchAt (indepOracle I recAns) ω r) : ℝ) ≤
              Kq * (n : ℝ) ^ (5 + γ) * Real.logb 2 n ∧
            numRec ((It n ρ).batchAt (indepOracle I recAns) ω r) ≤ Nord n γ) ∧
        ((It n ρ).output (indepOracle I recAns) ω = some IterOutput.fail ∨
          (∃ U, (It n ρ).output (indepOracle I recAns) ω = some (IterOutput.contract U) ∧
            I U ∧ (n : ℝ) / (5000 * Real.logb 2 n) ≤ (U.card : ℝ) ∧
            (It n ρ).Queried (indepOracle I recAns) ω (IQuery.indep U)) ∨
          (∃ R cert, (It n ρ).output (indepOracle I recAns) ω =
              some (IterOutput.defer R cert) ∧
            (2 : ℝ) ^ (-26 : ℤ) * n / Real.logb 2 n ≤ (R.card : ℝ) ∧
            ∀ x ∈ R, cert x ⊆ Finset.univ \ R ∧ I (cert x) ∧ ¬ I (insert x (cert x)) ∧
              (It n ρ).Queried (indepOracle I recAns) ω (IQuery.indep (cert x)) ∧
              (It n ρ).Queried (indepOracle I recAns) ω (IQuery.indep (insert x (cert x)))))) ∧
      tapeLaw {ω | (It n ρ).output (indepOracle I recAns) ω = some IterOutput.fail} ≤
        ENNReal.ofReal ((2 : ℝ) ^ (-(n : ℝ) / 2)) := by sorry

end ExactParallelSampling.QuasiUniform
