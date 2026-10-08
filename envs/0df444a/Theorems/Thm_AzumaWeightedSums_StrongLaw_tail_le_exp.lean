-- Prove2me | Theorems.Thm_AzumaWeightedSums_StrongLaw_tail_le_exp
-- name    : AzumaWeightedSums.StrongLaw.tail_le_exp
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:49:19.963981+00:00
-- url     : https://prove2.me/theorems/2eebcb0a-f558-4b18-b981-8219a541b26c
-- title:
--   Tail step of (4.16) — $P\{\sum_{j\le N} c_jx_j > \lambda\} \le \exp(-\lambda^2/(2\sum_{j\le N} c_j^2))$
-- statement:
--   Let $(x_n)_{n\ge1}$ be a sequence of martingale differences with respect to an increasing family $(\mathfrak A_n)$ of sub-$\sigma$-fields of a probability space, with $|x_n|\le1$ almost surely for every $n\ge1$. Let $N\ge 0$, let $c_1,\dots,c_N$ be real numbers with $\sum_{j=1}^N c_j^2 > 0$, and let $\lambda\ge0$. Then
--
--   $$P\Big\{\sum_{j=1}^{N} c_j x_j > \lambda\Big\} \le \exp\!\Big(-\frac{\lambda^2}{2\sum_{j=1}^{N} c_j^2}\Big).$$
--
--   This is the one-sided Azuma inequality with the constant used in the paper. In the proof of Theorem 3 it is applied with $N = n_{k+1}$, $c_j = a_{n_{k+1}-j+1}$ (so that the sum is $\bar S_{n_{k+1}}$) and $\lambda = (\varepsilon/2)A_{n_k}$, which gives the second line of (4.16): $P\{\bar S_{n_{k+1}} > (\varepsilon/2)A_{n_k}\} \le \exp\big(-\varepsilon^2A_{n_k}^2/(8\sum_{j=1}^{n_{k+1}} a_j^2)\big)$.
--
--   **Formalization Note** The probability is the real-valued measure of the event. The coefficients are an arbitrary real sequence $c$, of which only $c_1,\dots,c_N$ enter.
-- source:
--   Azuma, Weighted sums of certain dependent random variables, Tôhoku Math. J. 19 (1967), p. 366, proof of Theorem 3, display (4.16), second line (from (2.4) and Remark 1)

import Mathlib
import Definitions.Def_AzumaWeightedSums_IteratedLog_ClassG

namespace AzumaWeightedSums.StrongLaw

open MeasureTheory

/-- The tail step of (4.16) (Azuma 1967, proof of Theorem 3, p. 366), obtained from (2.4),
Remark 1 and Chebyshev's exponential inequality: for martingale differences with `|x_j| ≤ 1`
a.s., real coefficients `c_1, …, c_N` with `∑ c_j² > 0` and `λ ≥ 0`,
`P{∑_{j=1}^N c_j x_j > λ} ≤ exp(-λ² / (2 ∑_{j=1}^N c_j²))`. -/
theorem tail_le_exp {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (x : ℕ → Ω → ℝ)
    (hx : AzumaWeightedSums.IteratedLog.IsMartingaleDiff μ ℱ x) (hbd : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂μ, |x n ω| ≤ 1)
    (N : ℕ) (c : ℕ → ℝ) (hc : 0 < ∑ j ∈ Finset.Icc 1 N, c j ^ 2)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    μ.real {ω | lam < ∑ j ∈ Finset.Icc 1 N, c j * x j ω}
      ≤ Real.exp (-lam ^ 2 / (2 * ∑ j ∈ Finset.Icc 1 N, c j ^ 2)) := by sorry

end AzumaWeightedSums.StrongLaw
