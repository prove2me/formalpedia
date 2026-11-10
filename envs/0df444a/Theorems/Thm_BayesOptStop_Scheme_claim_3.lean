-- Prove2me | Theorems.Thm_BayesOptStop_Scheme_claim_3
-- name    : BayesOptStop.Scheme.claim_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:21:40.277401+00:00
-- url     : https://prove2.me/theorems/c29c96e3-0adf-4ba9-9237-95274b827b9f
-- title:
--   Claim 3 — accuracy and running time of the recursive estimator (Algorithm 3)
-- statement:
--   Suppose $0<\alpha_0\le1$ and $\alpha_{\ell+1}=1/(1+\ln(1/\alpha_\ell))$. For every integer $j\ge0$, sample path $\omega\in\Omega$ and accuracy parameters $0<\eta,\kappa<1$, the recursive estimator $W_j(\omega,\eta,\kappa)$ of Algorithm 3 returns $\widehat W_j(\omega)$ with $\widehat W_j(\omega)/W_j(\omega)\in[1-\eta,(1-\eta)^{-1}]$ with probability at least $1-\kappa$, in time $\mathrm{poly}\big(2^{j^2}(Kmn/(\alpha_0\eta\kappa))^{j+1}\big)$; more precisely in time
--   $$O\Big(756^{j^2}Kmn^{j+1}(\alpha_0\eta)^{-2j}\big(j+\ln\tfrac{n}{\alpha_0\kappa\eta}\big)^j\Big).$$
--   Formally: one admissible program of the unit-cost machine with CORREL oracle access, realizing the complete output law of Algorithm 3, and one universal constant $C$; the accuracy holds at every path whose value sequence has positive probability, the time bound on every path, tape and admissible oracle.
--
--   Differences from the source:
--   - encoding: the recursive estimator W_j(ω, η, κ) of Algorithm 3 returns Ŵ_j(ω) … in time … → one admissible program P whose output distribution equals lawMeasure (algorithm3Law I α₀ j ω η κ), with the printed accuracy and both runtime bounds; reason: algorithm3Law constructs all steps of Algorithm 3 with independent biased samples and fresh recursive calls; equality of output laws permits a machine implementation without replacing the specified estimator by an arbitrary one
--   - reading: running time counts arithmetic operations and oracle calls at unit cost (§2.1, p. 8) → worst-case number of steps of an `Admissible` program of the unit-cost randomized real RAM `Machine` (SmaleNinth core, integer memory, exp, log, uniform tape, observe/accept, oracle instructions; rational literals, no floor), over every path and every tape in the support; reason: the paper names no machine; exp and log at unit cost are needed by the algorithm (γ = 1/(1+ln(1/α)), (1−η)^{1/3}, ln(4n/δ)) and are read as arithmetic operations
--   - encoding: probability and value oracles taking any history h_t → an `Oracle` that must answer correctly at every history of positive probability (any list of value indices, length ≤ n) and may answer arbitrarily elsewhere; the claim holds for every such oracle; reason: the source is silent at zero-probability histories; quantifying over all answers there is the strongest reading
--   - encoding: O(·) and poly(·) → C · (bound) and C · (base)^C, one universal constant C chosen before every parameter, instance and oracle; reason: explicit constants
--   - encoding: with probability at least 1 − κ, over the algorithm's randomness → uniformTape measure of the success event ≥ 1 − κ; reason: the tape is the only randomness
--   - encoding: for every sample path ω ∈ Ω → accuracy for every path whose value sequence has positive probability (cylProb n ω > 0); time bound for every path; reason: W_j(ω) involves Z^(ℓ)_t at the prefixes of ω, undefined at null histories, where the oracle answers are arbitrary
--   - encoding: K, m, n are the instance sizes (at least 1) → 0 < K, 0 < m, 0 < n; reason: nondegeneracy; an instance has a world, a value and a time
--   - encoding: histories h_t are sequences of observed values; times t ∈ [n] are 1-based → paths ω : Fin n → Fin m of value indices, histories are value cylinders `Agree t` (first t values equal), times 0-based (the paper's X_t is X ⟨t-1⟩, Z_t at history length t); reason: Lean convention; conditioning is on values, so repeated v_q give the paper's filtration
-- source:
--   AmaniHamedani, Aouad, Işık, Kesselheim, Saberi (2026), Bayesian Optimal Stopping: Invincible Prophets and Achievable Philosophers, held STOC 2027 submission, SHA-256 fecfa05a3285ac21a7efbed099d2afed88a382dfcc9d91836b6e5210d70c4241, Claim 3, pp. 38–39 (proof App. B.4, pp. 41–44)

import Mathlib
import Definitions.Def_BayesOptStop_Scheme_Improvement
import Definitions.Def_BayesOptStop_Scheme_Algorithms
import Definitions.Def_BayesOptStop_Scheme_Machine

open MeasureTheory

namespace BayesOptStop.Scheme

/-- **Claim 3** (AmaniHamedani, Aouad, Işık, Kesselheim, Saberi 2026, held STOC 2027 submission,
SHA-256 fecfa05a…c4241, pp. 38–39): suppose `0 < α₀ ≤ 1` and `α_{ℓ+1} = 1/(1 + ln(1/α_ℓ))`. For every
integer `j ≥ 0`, sample path `ω` and `0 < η, κ < 1`, the recursive estimator `W_j(ω, η, κ)` returns
`Ŵ_j(ω)` with `Ŵ_j(ω)/W_j(ω) ∈ [1-η, (1-η)^{-1}]` with probability at least `1 - κ` in time
`poly(2^{j²} (Kmn/(α₀ηκ))^{j+1})`; more precisely in time
`O(756^{j²} K m n^{j+1} (α₀η)^{-2j} (j + ln(n/(α₀κη)))^j)`.
One program, one constant `C` for both `O(·)` and `poly(·)`, uniform in every parameter, instance
and admissible oracle; the time bound holds on every path and every tape. -/
theorem claim_3 :
    ∃ C : ℝ, 0 < C ∧ ∃ P : Program, Admissible P ∧
      ∀ (K m n : ℕ), 0 < K → 0 < m → 0 < n →
      ∀ I : Instance K m n, I.Valid → I.Standing →
      ∀ o : Oracle, I.OracleAdmissible o →
      ∀ (α₀ η κ : ℝ), 0 < α₀ → α₀ ≤ 1 → 0 < η → η < 1 → 0 < κ → κ < 1 →
      ∀ (j : ℕ) (ω : Fin n → Fin m),
        (0 < I.cylProb n ω →
          Measure.map (output P [] o (I.inputW α₀ η κ j ω)) uniformTape =
            lawMeasure (I.algorithm3Law α₀ j ω η κ) ∧
          ENNReal.ofReal (1 - κ) ≤ uniformTape {u |
            (1 - η) * I.Wseq α₀ j ω ≤ output P [] o (I.inputW α₀ η κ j ω) u ∧
              output P [] o (I.inputW α₀ η κ j ω) u ≤ (1 - η)⁻¹ * I.Wseq α₀ j ω}) ∧
        ∀ u : ℕ → ℝ, TapeInSupport u →
          HaltsWithin P [] o (I.inputW α₀ η κ j ω) u
              (C * (756 : ℝ) ^ (j ^ 2) * ((K : ℝ) * m * (n : ℝ) ^ (j + 1)) *
                ((α₀ * η) ^ (2 * j))⁻¹ * ((j : ℝ) + Real.log (n / (α₀ * κ * η))) ^ j) ∧
            HaltsWithin P [] o (I.inputW α₀ η κ j ω) u
              (C * ((2 : ℝ) ^ (j ^ 2) * ((K : ℝ) * m * n / (α₀ * η * κ)) ^ (j + 1)) ^ C) := by sorry

end BayesOptStop.Scheme
