-- Prove2me | Theorems.Thm_DeepQOperator_eq_47
-- name    : DeepQOperator.eq_47
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:08:40.752387+00:00
-- url     : https://prove2.me/theorems/42c868b8-7518-48b5-b789-314d84320cc0
-- title:
--   (46)–(47): median amplification gives $\|\widetilde b-b\|_\infty\le1/16$ with probability $1-\delta$
-- statement:
--   Let $m\ge2$, $0<\delta\le1/2$, $R=2\lceil\log_2(m/\delta)\rceil+1$, and let $V_{t,k}$ ($t\le R$, $k\le1024$) be independent uniform addresses. Fix an address $a\in[-1,1]^n$. Then:
--   1. for each $i$, $\Pr\{|\mathrm{median}_tU_{t,i}-b_i|>3/64\}\le2^{-R/2}$, and $2^{-R/2}\le\delta/m$;
--   2. for every sample list, the five-bit average (44) satisfies $|\widetilde U_{t,i}-U_{t,i}|\le1/64$ (46);
--   3. an odd median is $1$-Lipschitz in the coordinate supremum norm;
--   4. the event $G=\{\|\widetilde b-b\|_\infty\le1/16\}$, with $\widetilde b_i=\mathrm{median}_t\widetilde U_{t,i}$, has
--   $$\Pr(G)\ge1-\delta.\tag{47}$$
--
--   $G$ is the success event of the first stage of Theorem 2's protocol; it is a per-input probability, not one seed good for all inputs.
--
--   **Formalization Note** The seed is the uniform measure on `Fin R → Fin 1024 → Addr m`. The median is the $\frac{R+1}2$-th order statistic.
--
--   Differences from the source:
--   - generalization: δ = min{1/2, 16ε/γ} of (8) → every δ ∈ (0, 1/2]; reason: the δ of (8) lies in (0, 1/2]
--   - generalization: the median of the R repetitions → 1-Lipschitz for every odd number of entries; reason: R is odd
--   - encoding: ≤ 2^R(1/8)^{R/2} = 2^{−R/2} ≤ δ/m → ≤ 2^{−R/2} and 2^{−R/2} ≤ δ/m; reason: 2^R(1/8)^{R/2} = 2^{−R/2} is arithmetic
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), Appendix E.2, eqs. (46)–(47), p.24 (PDF p.27)

import Mathlib
import Definitions.Def_DeepQOperator_Family
import Definitions.Def_DeepQOperator_Quantizer
import Definitions.Def_DeepQOperator_ReplyProtocol
import Definitions.Def_DeepQOperator_Sampling

open MeasureTheory

namespace DeepQOperator

/-- **Median amplification, (46) and (47)** (Q. Qi, *Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions*,
STOC 2027 submission (manuscript sha256 9f8f3285…), Appendix E.2, p.24, PDF p.27).

Let `m ≥ 2`, `δ ∈ (0, 1/2]`, `R = 2⌈log₂(m/δ)⌉ + 1`, and let `V_{t,k}` (`t ≤ R`, `k ≤ 1024`) be
independent uniform addresses. Fix an address `a ∈ [-1,1]^n`. Then:
1. `Pr{|median_t U_{t,i} - b_i| > 3/64} ≤ 2^{-R/2}` and `2^{-R/2} ≤ δ/m`;
2. (46) for every sample list, `|Ũ_{t,i} - U_{t,i}| ≤ 1/64`, with `Ũ` the five-bit average (44);
3. an odd median is 1-Lipschitz in the coordinate supremum norm;
4. (47) the event `G = {∥b̃ - b∥_∞ ≤ 1/16}`, `b̃_i = median_t Ũ_{t,i}`, has `Pr(G) ≥ 1 - δ`.

**Formalization Note.** The seed is `ω : Fin R → Fin 1024 → Addr m` with the uniform measure
`samplingSeedLaw m R`; `U_{t,i} = sampleMean i (ω t) a` and `Ũ_{t,i} = sampleMean i (ω t) (Q_5 ∘ a)`.
`R` uses `⌈·⌉₊`. The paper's `δ` is the `δ` of (8); the statement holds for every `δ ∈ (0, 1/2]`,
which contains that value. -/
theorem eq_47 (m : ℕ) (hm : 2 ≤ m) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (θ : Coord m → ℝ) (ha : ∀ v : Addr m, θ (Sum.inl v) ∈ Set.Icc (-1 : ℝ) 1) :
    (∀ i : Fin m,
      samplingSeedLaw m (2 * ⌈Real.logb 2 ((m : ℝ) / δ)⌉₊ + 1)
          {ω | 3 / 64 < |oddMedian (fun t => sampleMean i (ω t) (fun w => θ (Sum.inl w))) -
            bScore m i θ|} ≤
        ENNReal.ofReal ((2 : ℝ) ^ (-((2 * ⌈Real.logb 2 ((m : ℝ) / δ)⌉₊ + 1 : ℕ) : ℝ) / 2))) ∧
    (2 : ℝ) ^ (-((2 * ⌈Real.logb 2 ((m : ℝ) / δ)⌉₊ + 1 : ℕ) : ℝ) / 2) ≤ δ / m ∧
    (∀ (ω : Fin (2 * ⌈Real.logb 2 ((m : ℝ) / δ)⌉₊ + 1) → Fin sampleSize → Addr m) t (i : Fin m),
      |sampleMean i (ω t) (fun w => qRound 5 (θ (Sum.inl w))) -
        sampleMean i (ω t) (fun w => θ (Sum.inl w))| ≤ 1 / 64) ∧
    (∀ (R : ℕ), Odd R → ∀ (x y : Fin R → ℝ) (ρ : ℝ), (∀ t, |x t - y t| ≤ ρ) →
      |oddMedian x - oddMedian y| ≤ ρ) ∧
    ENNReal.ofReal (1 - δ) ≤
      samplingSeedLaw m (2 * ⌈Real.logb 2 ((m : ℝ) / δ)⌉₊ + 1)
        {ω | ∀ i : Fin m,
          |oddMedian (fun t => sampleMean i (ω t) (fun w => qRound 5 (θ (Sum.inl w)))) -
            bScore m i θ| ≤ 1 / 16} := by sorry

end DeepQOperator
