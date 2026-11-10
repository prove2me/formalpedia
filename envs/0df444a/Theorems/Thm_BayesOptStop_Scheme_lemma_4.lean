-- Prove2me | Theorems.Thm_BayesOptStop_Scheme_lemma_4
-- name    : BayesOptStop.Scheme.lemma_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:20:23.890635+00:00
-- url     : https://prove2.me/theorems/1b522b62-2222-4f40-9e86-9c64923a0edd
-- title:
--   Lemma 4 — efficient estimation of $Z^{(j)}_t(h_t)$
-- statement:
--   Suppose $0<\alpha_0<1$ and $0<\varepsilon,\delta<1$. For each $j\ge0$, time $t\in[n]$ and history $h_t$, one can compute $L^{(j)}_t(h_t)$ with $L^{(j)}_t(h_t)/Z^{(j)}_t(h_t)\in[1-\varepsilon,1]$ with probability at least $1-\delta$ in time $\mathrm{poly}\big(2^{j^2}(Kmn/(\alpha_0\varepsilon\delta))^{j+1}\big)$; more precisely in time
--   $$O\Big(\zeta^{j^2}Kmn^{j+1}(\alpha_0\varepsilon)^{-(2j+2)}\big(j+\ln\tfrac{n}{\alpha_0\delta\varepsilon}\big)^{j+1}\Big),\qquad\zeta=2^{19}.$$
--   Formally: one admissible program of the unit-cost machine with CORREL oracle access and one universal constant $C$; the accuracy holds at every reachable history, the time bound at every history, tape and admissible oracle.
--
--   Differences from the source:
--   - reading: we can compute L^(j)_t(h_t) … in time … → there are a constant C > 0 and one admissible machine program P, reading j, t, h_t, α₀, ε, δ, v from its input, whose output (real cell −1) has the accuracy and the running time; reason: 'we can compute' asserts an algorithm in the §2.1 cost model
--   - reading: running time counts arithmetic operations and oracle calls at unit cost (§2.1, p. 8) → worst-case number of steps of an `Admissible` program of the unit-cost randomized real RAM `Machine` (SmaleNinth core, integer memory, exp, log, uniform tape, observe/accept, oracle instructions; rational literals, no floor), over every path and every tape in the support; reason: the paper names no machine; exp and log at unit cost are needed by the algorithm (γ = 1/(1+ln(1/α)), (1−η)^{1/3}, ln(4n/δ)) and are read as arithmetic operations
--   - encoding: probability and value oracles taking any history h_t → an `Oracle` that must answer correctly at every history of positive probability (any list of value indices, length ≤ n) and may answer arbitrarily elsewhere; the claim holds for every such oracle; reason: the source is silent at zero-probability histories; quantifying over all answers there is the strongest reading
--   - encoding: O(·) and poly(·) → C · (bound) and C · (base)^C, one universal constant C chosen before every parameter, instance and oracle; reason: explicit constants
--   - encoding: with probability at least 1 − δ → uniformTape measure of the success event ≥ 1 − δ; reason: the tape is the only randomness
--   - encoding: a history h_t → the history (canonical value indices) of a path ω at time t ∈ [1, n]; accuracy at reachable histories (Pr[h_t] > 0), time bound at every history; reason: Z^(j)_t is undefined at a null history, where the oracle answers are arbitrary
--   - encoding: K, m, n are the instance sizes (at least 1) → 0 < K, 0 < m, 0 < n; reason: nondegeneracy
--   - encoding: histories h_t are sequences of observed values; times t ∈ [n] are 1-based → paths ω : Fin n → Fin m of value indices, histories are value cylinders `Agree t` (first t values equal), times 0-based (the paper's X_t is X ⟨t-1⟩, Z_t at history length t); reason: Lean convention; conditioning is on values, so repeated v_q give the paper's filtration
-- source:
--   AmaniHamedani, Aouad, Işık, Kesselheim, Saberi (2026), Bayesian Optimal Stopping: Invincible Prophets and Achievable Philosophers, held STOC 2027 submission, SHA-256 fecfa05a3285ac21a7efbed099d2afed88a382dfcc9d91836b6e5210d70c4241, Lemma 4, p. 19 (proof App. B.3, pp. 38–41)

import Mathlib
import Definitions.Def_BayesOptStop_Scheme_Improvement
import Definitions.Def_BayesOptStop_Scheme_Machine

open MeasureTheory

namespace BayesOptStop.Scheme

/-- **Lemma 4** (AmaniHamedani, Aouad, Işık, Kesselheim, Saberi 2026, held STOC 2027 submission,
SHA-256 fecfa05a…c4241, p. 19): suppose `0 < α₀ < 1` and `0 < ε, δ < 1`. For each `j ≥ 0`, time
`t ∈ [n]` and history `h_t`, we can compute `L^(j)_t(h_t)` with `L^(j)_t(h_t)/Z^(j)_t(h_t) ∈ [1-ε, 1]`
with probability at least `1 - δ` in time `poly(2^{j²} (Kmn/(α₀εδ))^{j+1})`; more precisely in time
`O(ζ^{j²} K m n^{j+1} (α₀ε)^{-(2j+2)} (j + ln(n/(α₀δε)))^{j+1})` with `ζ = 2^19`.
One program, one constant `C` for both `O(·)` and `poly(·)`, uniform in every parameter, instance
and admissible oracle; the time bound holds on every history and every tape. -/
theorem lemma_4 :
    ∃ C : ℝ, 0 < C ∧ ∃ P : Program, Admissible P ∧
      ∀ (K m n : ℕ), 0 < K → 0 < m → 0 < n →
      ∀ I : Instance K m n, I.Valid → I.Standing →
      ∀ o : Oracle, I.OracleAdmissible o →
      ∀ (α₀ ε δ : ℝ), 0 < α₀ → α₀ < 1 → 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      ∀ (j t : ℕ), 1 ≤ t → t ≤ n → ∀ ω : Fin n → Fin m,
        (0 < I.cylProb t ω →
          ENNReal.ofReal (1 - δ) ≤ uniformTape {u |
            (1 - ε) * I.Zseq α₀ j t ω ≤ output P [] o (I.inputZ α₀ ε δ j t ω) u ∧
              output P [] o (I.inputZ α₀ ε δ j t ω) u ≤ I.Zseq α₀ j t ω}) ∧
        ∀ u : ℕ → ℝ, TapeInSupport u →
          HaltsWithin P [] o (I.inputZ α₀ ε δ j t ω) u
              (C * ((2 : ℝ) ^ 19) ^ (j ^ 2) * ((K : ℝ) * m * (n : ℝ) ^ (j + 1)) *
                ((α₀ * ε) ^ (2 * j + 2))⁻¹ * ((j : ℝ) + Real.log (n / (α₀ * δ * ε))) ^ (j + 1)) ∧
            HaltsWithin P [] o (I.inputZ α₀ ε δ j t ω) u
              (C * ((2 : ℝ) ^ (j ^ 2) * ((K : ℝ) * m * n / (α₀ * ε * δ)) ^ (j + 1)) ^ C) := by sorry

end BayesOptStop.Scheme
