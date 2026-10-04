-- Prove2me | Theorems.Thm_AzumaWeightedSums_IteratedLog_max_tail_le
-- name    : AzumaWeightedSums.IteratedLog.max_tail_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T05:31:13.93533+00:00
-- url     : https://prove2.me/theorems/af2631f5-e11d-4ca9-9a20-854af2cef216
-- title:
--   Maximal tail bound $P\{S_n^*>\lambda\}\le 8\exp(-\lambda^2/(2\sum b_k^2))$ (proof of Theorem 2)
-- statement:
--   Let $(x_n)_{n\ge1}$ belong to class [G] with $\tau(x_n)\le1$ for all $n$, let $(b_k)$ be a real sequence, $n\ge1$, and suppose $V_n=\sum_{k=1}^n b_k^2>0$. With $S_n^*=\max_{1\le m\le n}|\sum_{k=1}^m b_kx_k|$, for every $\lambda\ge0$,
--   $$
--   P\{S_n^*>\lambda\}\le 8\exp\Big(-\frac{\lambda^2}{2V_n}\Big).
--   $$
--
--   This is the bound that, in the proof of Theorem 2, "the Tchebycheff inequality and (2.3)" yield: a maximal Azuma–Hoeffding inequality for weighted sums of conditionally sub-Gaussian martingale differences. It is the probabilistic input to the Borel–Cantelli argument for Theorem 2.
--
--   **Formalization Note** The probability is the measure (in $[0,\infty]$) of the set where $S_n^*>\lambda$. The paper's printed proof of Theorem 2 writes the increment $D_{n_{k+1}}^2-D_{n_k}^2$ in the denominator of the corresponding exponent; Chebyshev's exponential inequality and (2.3) give the full sum of squared weights, which is what is stated here.
-- source:
--   Azuma, Weighted sums of certain dependent random variables, Tôhoku Math. J. 19 (1967), https://doi.org/10.2748/tmj/1178243286, pp. 362–363, proof of Theorem 2 ("using the Tchebycheff inequality and (2.3)")

import Mathlib
import Definitions.Def_AzumaWeightedSums_IteratedLog_ClassG
import Definitions.Def_AzumaWeightedSums_IteratedLog_WeightedSums

open MeasureTheory ProbabilityTheory Filter Topology

namespace AzumaWeightedSums.IteratedLog

/-- The maximal tail bound that "the Tchebycheff inequality and (2.3)" give in the proof of
Theorem 2 of Azuma 1967 (pp. 362–363): under [G] with `τ(x_n) ≤ 1`, for every `n`, every
real sequence `(b_k)` with `Σ_{k=1}^n b_k² > 0` and every `λ ≥ 0`,
`P{S_n^* > λ} ≤ 8 exp(−λ² / (2 Σ_{k=1}^n b_k²))`. -/
theorem max_tail_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {x : ℕ → Ω → ℝ}
    (hx : IsCondSubgaussianOne μ ℱ x) (b : ℕ → ℝ) (n : ℕ) (hb : 0 < sqWeightSum b n)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    μ {ω | lam < maxAbsWeightedSum b x n ω}
      ≤ ENNReal.ofReal (8 * Real.exp (-(lam ^ 2) / (2 * sqWeightSum b n))) := by sorry

end AzumaWeightedSums.IteratedLog
