-- Prove2me | Theorems.Thm_AzumaWeightedSums_IteratedLog_lemma2_mgf_max_le
-- name    : AzumaWeightedSums.IteratedLog.lemma2_mgf_max_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T05:30:48.132529+00:00
-- url     : https://prove2.me/theorems/de12479a-7e15-4d07-b7a5-0f70ef2eee56
-- title:
--   Lemma 2 — $E\exp(tS_n^*)\le 8\exp(\tfrac{t^2}{2}\sum b_k^2)$
-- statement:
--   Let $(x_n)_{n\ge1}$ belong to class [G] with $\tau(x_n)\le1$ for all $n$, let $(b_k)$ be an arbitrary real sequence and put
--   $$
--   S_n^*(\omega)=\max_{1\le m\le n}\Big|\sum_{k=1}^m b_kx_k(\omega)\Big|.
--   $$
--   Then for every $n$ and every real $t$,
--   $$
--   E\{\exp(tS_n^*)\}\le 8\exp\Big(\frac{t^2}{2}\sum_{k=1}^n b_k^2\Big).
--   $$
--
--   This is Lemma 2 of Azuma's paper, display (2.3): the maximal partial sum has the same sub-Gaussian moment-generating bound as the last partial sum, at the price of the factor $8$. It is the estimate behind the tail bounds in the proof of Theorem 2.
--
--   **Formalization Note** The expectation is a lower Lebesgue integral in $[0,\infty]$, so the statement also asserts finiteness. $S_0^*=0$, and the case $n=0$ reads $1\le 8$. The inequality is stated for every real $t$ (for $t<0$ the left side is at most $1$).
-- source:
--   Azuma, Weighted sums of certain dependent random variables, Tôhoku Math. J. 19 (1967), https://doi.org/10.2748/tmj/1178243286, p. 358, Lemma 2, display (2.3) (proof ends p. 359)

import Mathlib
import Definitions.Def_AzumaWeightedSums_IteratedLog_ClassG
import Definitions.Def_AzumaWeightedSums_IteratedLog_WeightedSums

open MeasureTheory ProbabilityTheory Filter Topology

namespace AzumaWeightedSums.IteratedLog

/-- Azuma 1967, Lemma 2, display (2.3), p. 358: under [G] with `τ(x_n) ≤ 1`,
`E{exp(t S_n^*)} ≤ 8 exp((t²/2) Σ_{k=1}^n b_k²)` for every `n`, every real sequence `(b_k)`
and every real `t`, where `S_n^* = max_{1 ≤ m ≤ n} |Σ_{k=1}^m b_k x_k|`. -/
theorem lemma2_mgf_max_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {x : ℕ → Ω → ℝ}
    (hx : IsCondSubgaussianOne μ ℱ x) (b : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (t * maxAbsWeightedSum b x n ω)) ∂μ
      ≤ ENNReal.ofReal (8 * Real.exp (t ^ 2 / 2 * sqWeightSum b n)) := by sorry

end AzumaWeightedSums.IteratedLog
