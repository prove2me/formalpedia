-- Prove2me | Theorems.Thm_DeepQOperator_eq_45
-- name    : DeepQOperator.eq_45
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:08:31.060956+00:00
-- url     : https://prove2.me/theorems/ceba587c-822c-4817-8f4e-226aef13611a
-- title:
--   (45): one repetition of uniform coordinate sampling estimates each Walsh score
-- statement:
--   Let $s=1024$ and let $V_1,\dots,V_s$ be independent uniform addresses in $\{0,1\}^r$. Fix an address $a\in[-1,1]^n$ and $i<m$. Each sample satisfies
--   $$\mathbb E\big[c_i(V_k)a_{V_k}/2\big]=\frac1{2n}\sum_{w\in\{0,1\}^r}c_i(w)a_w=b_i,$$
--   and the signed average $U_i=(2s)^{-1}\sum_kc_i(V_k)a_{V_k}$ satisfies
--   $$\mathbb EU_i=b_i,\qquad \mathrm{Var}(U_i)\le\frac1{4s}=\frac1{4096},\qquad \Pr\{|U_i-b_i|>3/64\}\le\frac19.\tag{45}$$
--
--   This is the per-repetition success bound that median amplification turns into a high-probability uniform estimate.
--
--   **Formalization Note** The draws are the uniform probability measure on `Fin 1024 → Addr m`. One repetition is stated; all repetitions have the same law.
--
--   Differences from the source:
--   - encoding: Pr{|U_{t,i} − b_i| > 3/64} ≤ 1/9 ≤ 1/8 → ≤ 1/9; reason: 1/9 ≤ 1/8 is arithmetic
--   - encoding: repetition t, draws V_{t,k} i.i.d. uniform → one repetition: the uniform measure on Fin 1024 → Addr m; reason: the repetitions are identically distributed
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), Appendix E.2, eq. (45), p.24 (PDF p.27)

import Mathlib
import Definitions.Def_DeepQOperator_Family
import Definitions.Def_DeepQOperator_Quantizer
import Definitions.Def_DeepQOperator_ReplyProtocol
import Definitions.Def_DeepQOperator_Sampling

open MeasureTheory

namespace DeepQOperator

/-- **(45)** (Q. Qi, *Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions*,
STOC 2027 submission (manuscript sha256 9f8f3285…), Appendix E.2, p.24, PDF p.27).

Let `s = 1024` and `V_1, …, V_s` independent uniform addresses in `{0,1}^r`. For every address
`a ∈ [-1,1]^n` and `i < m`: `E[c_i(V_k) a_{V_k}/2] = (1/(2n)) Σ_w c_i(w) a_w = b_i`, and the average
`U_i = (2s)^{-1} Σ_k c_i(V_k) a_{V_k}` satisfies `E U_i = b_i`, `Var(U_i) ≤ 1/(4s) = 1/4096` and
`Pr{|U_i - b_i| > 3/64} ≤ 1/9` (`≤ 1/8`).

**Formalization Note.** The `s` independent uniform draws are the uniform measure on
`Fin 1024 → Addr m`; expectations are Bochner integrals of functions on this finite space, and the
variance is `ProbabilityTheory.variance`. `U_i` is `sampleMean i V a`. The final `≤ 1/8` follows from
`≤ 1/9` and is not restated. -/
theorem eq_45 (m : ℕ) (hm : 2 ≤ m) (θ : Coord m → ℝ)
    (ha : ∀ v : Addr m, θ (Sum.inl v) ∈ Set.Icc (-1 : ℝ) 1) (i : Fin m) :
    (∀ k : Fin sampleSize,
      ∫ V, walsh (rr m) i (V k) * θ (Sum.inl (V k)) / 2
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin sampleSize → Addr m))) =
        bScore m i θ) ∧
    ∫ V, sampleMean i V (fun w => θ (Sum.inl w))
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin sampleSize → Addr m))) = bScore m i θ ∧
    ProbabilityTheory.variance (fun V => sampleMean i V (fun w => θ (Sum.inl w)))
        (ProbabilityTheory.uniformOn (Set.univ : Set (Fin sampleSize → Addr m))) ≤
      1 / (4 * (sampleSize : ℝ)) ∧
    1 / (4 * (sampleSize : ℝ)) = 1 / 4096 ∧
    (ProbabilityTheory.uniformOn (Set.univ : Set (Fin sampleSize → Addr m)))
        {V | 3 / 64 < |sampleMean i V (fun w => θ (Sum.inl w)) - bScore m i θ|} ≤
      ENNReal.ofReal (1 / 9) := by sorry

end DeepQOperator
