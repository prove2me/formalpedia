-- Prove2me | Theorems.Thm_AzumaWeightedSums_StrongLaw_remark1_condMGF_le
-- name    : AzumaWeightedSums.StrongLaw.remark1_condMGF_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:49:08.865467+00:00
-- url     : https://prove2.me/theorems/2c67ace7-7031-49a6-b98d-2f789e7452e4
-- title:
--   Remark 1 — $E\{\exp(tx_n)\mid\mathfrak A_{n-1}\} \le \cosh(tK_n) \le \exp(t^2K_n^2/2)$ for bounded martingale differences
-- statement:
--   Let $(\Omega,\mathfrak A,P)$ be a probability space with an increasing family $(\mathfrak A_n)$ of sub-$\sigma$-fields, and let $(x_n)_{n\ge1}$ be a sequence of martingale differences with respect to $(\mathfrak A_n)$. Let $(K_n)_{n\ge1}$ be real numbers with $|x_n|\le K_n$ almost surely for every $n\ge1$. Then for every $n = 1,2,\dots$ and every real $t$,
--
--   $$E\{\exp(t x_n)\mid \mathfrak A_{n-1}\} \le \cosh(t K_n) \quad\text{a.s.}, \qquad E\{\exp(t x_n)\mid \mathfrak A_{n-1}\} \le \exp\!\big(t^2K_n^2/2\big) \quad\text{a.s.}$$
--
--   In the paper's terminology, $(x_n)$ therefore has property [G] with $\tau(x_n)\le K_n$: a bounded martingale difference is conditionally sub-Gaussian with variance proxy $K_n^2$. This is the input that lets the moment-generating-function bound (2.4) be applied to the bounded martingale differences of Theorem 3.
--
--   **Formalization Note** Each almost-sure inequality holds for each fixed $t$ (the paper's "for every $t$, a.s." order of quantifiers). Integrability of $\exp(tx_n)$ is not assumed; it follows from the boundedness of $x_n$.
-- source:
--   Azuma, Weighted sums of certain dependent random variables, Tôhoku Math. J. 19 (1967), p. 358, Remark 1

import Mathlib
import Definitions.Def_AzumaWeightedSums_IteratedLog_ClassG

namespace AzumaWeightedSums.StrongLaw

open MeasureTheory

/-- Remark 1 (Azuma 1967, p. 358). If `(x_n)` is a sequence of martingale differences with
`|x_n| ≤ K_n` a.s. for all `n`, then for `n = 1, 2, …` and every real `t`,
`E{exp(t x_n) | 𝔄_{n-1}} ≤ cosh(t K_n) ≤ exp(t² K_n² / 2)` a.s. -/
theorem remark1_condMGF_le {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (x : ℕ → Ω → ℝ)
    (hx : AzumaWeightedSums.IteratedLog.IsMartingaleDiff μ ℱ x) (K : ℕ → ℝ)
    (hK : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂μ, |x n ω| ≤ K n) :
    ∀ n : ℕ, 1 ≤ n → ∀ t : ℝ,
      (μ[fun ω => Real.exp (t * x n ω) | ℱ (n - 1)]
          ≤ᵐ[μ] fun _ => Real.cosh (t * K n)) ∧
      (μ[fun ω => Real.exp (t * x n ω) | ℱ (n - 1)]
          ≤ᵐ[μ] fun _ => Real.exp (t ^ 2 * K n ^ 2 / 2)) := by sorry

end AzumaWeightedSums.StrongLaw
