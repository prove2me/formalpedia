-- Prove2me | Theorems.Thm_BayesOptStop_Scheme_theorem_3
-- name    : BayesOptStop.Scheme.theorem_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:18:50.246196+00:00
-- url     : https://prove2.me/theorems/08a08442-4c2a-4200-ab2f-68b07e1fb8fb
-- title:
--   Theorem 3 — an approximation scheme against the Bayes-optimal online value ON (CORREL, NON-IID and IID)
-- statement:
--   For every $0<\varepsilon\le1$ there is an algorithm $A$ such that for any instance of the Bayesian optimal stopping problem in the CORREL model, $r(A)\ge(1-\varepsilon)\mathrm{ON}$, and $A$ runs in time $\mathrm{poly}\big(Kmn^{1/\varepsilon+\log^*n}\cdot(1/\varepsilon)^{1/\varepsilon^2}\big)$. In the NON-IID model the exponent of $n$ in the running time is $1/\varepsilon+\log^*(\min\{n,2K\})$, and in the IID model it is $1/\varepsilon$.
--
--   Formally: there is one universal constant $C>0$, chosen before $\varepsilon$, such that for every $\varepsilon\in(0,1]$ there are three admissible programs of the unit-cost randomized real RAM — one with probability- and value-oracle access (CORREL), two oracle-free ones reading $\pi$ and the PMFs (NON-IID, IID) — whose expected reward is at least $(1-\varepsilon)\mathrm{ON}$ on every valid instance of the class satisfying the standing assumption (and, for CORREL, every admissible oracle), and which halt on every path and every tape within $C\cdot(Kmn^{e}(1/\varepsilon)^{1/\varepsilon^2})^C$ steps, $e$ the class's exponent.
--
--   Differences from the source:
--   - reading: running time counts arithmetic operations and oracle calls at unit cost (§2.1, p. 8) → worst-case number of steps of an `Admissible` program of the unit-cost randomized real RAM `Machine` (SmaleNinth core, integer memory, exp, log, uniform tape, observe/accept, oracle instructions; rational literals, no floor), over every path and every tape in the support; reason: the paper names no machine; exp and log at unit cost are needed by the algorithm (γ = 1/(1+ln(1/α)), (1−η)^{1/3}, ln(4n/δ)) and are read as arithmetic operations
--   - encoding: probability and value oracles taking any history h_t → an `Oracle` that must answer correctly at every history of positive probability (any list of value indices, length ≤ n) and may answer arbitrarily elsewhere; the claim holds for every such oracle; reason: the source is silent at zero-probability histories; quantifying over all answers there is the strongest reading
--   - encoding: poly(·) with the program depending on ε → ∃ C > 0 before ε; for each ε ∃ program; steps ≤ C·(base)^C; ε is also placed in the input memory; reason: explicit universal constant; rational literals cannot encode an irrational ε
--   - encoding: the algorithm observes X_1, X_2, … online and selects irrevocably → `observe` reveals the canonical index (least q with the same value) of the next observation, `accept` selects the latest and halts; never selecting earns 0; reason: the canonical index carries exactly the observed value
--   - encoding: NON-IID and IID: the PMFs (and π) are given → oracle-free programs with K, m, n and ε, v, π and the PMF table (row-major) in input memory; reason: App. A.2: the algorithm reads the PMFs, not oracles
--   - encoding: log* n → PredAdvice.logStar (base 2, natural argument); reason: the published definition; the base changes log* by an additive constant only
--   - encoding: K, m, n are the instance sizes (at least 1) → 0 < K, 0 < m, 0 < n; reason: nondegeneracy
--   - encoding: histories h_t are sequences of observed values; times t ∈ [n] are 1-based → paths ω : Fin n → Fin m of value indices, histories are value cylinders `Agree t` (first t values equal), times 0-based (the paper's X_t is X ⟨t-1⟩, Z_t at history length t); reason: Lean convention; conditioning is on values, so repeated v_q give the paper's filtration
-- source:
--   AmaniHamedani, Aouad, Işık, Kesselheim, Saberi (2026), Bayesian Optimal Stopping: Invincible Prophets and Achievable Philosophers, held STOC 2027 submission, SHA-256 fecfa05a3285ac21a7efbed099d2afed88a382dfcc9d91836b6e5210d70c4241, Theorem 3, p. 10 (proof §3.4.1, p. 21)

import Mathlib
import Definitions.Def_PredAdvice_logStar
import Definitions.Def_BayesOptStop_Scheme_Machine

open MeasureTheory

namespace BayesOptStop.Scheme

/-- **Theorem 3** (AmaniHamedani, Aouad, Işık, Kesselheim, Saberi 2026, held STOC 2027 submission,
SHA-256 fecfa05a…c4241, p. 10): for every `0 < ε ≤ 1` there is an algorithm `A` such that for any instance
in the CORREL model, `r(A) ≥ (1 - ε) ON`, and `A` runs in time
`poly(K m n^{1/ε + log* n} (1/ε)^{1/ε²})`. In the NON-IID model the exponent of `n` is
`1/ε + log*(min{n, 2K})`, and in the IID model it is `1/ε`.
One universal constant `C` for the polynomial, chosen before `ε`; the program may depend on `ε`.
CORREL: access through admissible probability and value oracles; NON-IID / IID: the prior and
PMFs in input memory, no oracle. The time bound is worst case over every path and tape. -/
theorem theorem_3 :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (∃ P : Program, Admissible P ∧
        ∀ (K m n : ℕ), 0 < K → 0 < m → 0 < n →
        ∀ I : Instance K m n, I.Valid → I.Standing →
        ∀ o : Oracle, I.OracleAdmissible o →
          (1 - ε) * I.ON ≤ I.programReward P o (I.correlInput ε) ∧
            ∀ (ω : Fin n → Fin m) (u : ℕ → ℝ), TapeInSupport u →
              HaltsWithin P (I.obsList ω) o (I.correlInput ε) u
                (C * ((K : ℝ) * m * (n : ℝ) ^ (1 / ε + (PredAdvice.logStar n : ℝ)) *
                  (1 / ε) ^ (1 / ε ^ 2)) ^ C)) ∧
      (∃ P : Program, Admissible P ∧ OracleFree P ∧
        ∀ (K m n : ℕ), 0 < K → 0 < m → 0 < n →
        ∀ D : NonIIDData K m n, D.Valid → D.toInstance.Standing →
          (1 - ε) * D.toInstance.ON ≤ D.toInstance.programReward P Oracle.zero (D.input ε) ∧
            ∀ (ω : Fin n → Fin m) (u : ℕ → ℝ), TapeInSupport u →
              HaltsWithin P (D.toInstance.obsList ω) Oracle.zero (D.input ε) u
                (C * ((K : ℝ) * m *
                  (n : ℝ) ^ (1 / ε + (PredAdvice.logStar (min n (2 * K)) : ℝ)) *
                  (1 / ε) ^ (1 / ε ^ 2)) ^ C)) ∧
      (∃ P : Program, Admissible P ∧ OracleFree P ∧
        ∀ (K m n : ℕ), 0 < K → 0 < m → 0 < n →
        ∀ D : IIDData K m, D.Valid → (D.toInstance n).Standing →
          (1 - ε) * (D.toInstance n).ON ≤
              (D.toInstance n).programReward P Oracle.zero (D.input n ε) ∧
            ∀ (ω : Fin n → Fin m) (u : ℕ → ℝ), TapeInSupport u →
              HaltsWithin P ((D.toInstance n).obsList ω) Oracle.zero (D.input n ε) u
                (C * ((K : ℝ) * m * (n : ℝ) ^ (1 / ε) * (1 / ε) ^ (1 / ε ^ 2)) ^ C)) := by sorry

end BayesOptStop.Scheme
