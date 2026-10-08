-- Prove2me | Theorems.Thm_DynSampleSize_Stoch_sample_mean_variance
-- name    : DynSampleSize.Stoch.sample_mean_variance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:28:37.9156+00:00
-- url     : https://prove2.me/theorems/de4bdf3c-8110-40dd-9138-d4fac8b59997
-- title:
--   §4.2, p. 12 — variance of the batch gradient, $\|\mathrm{Var}(g)\|_1 \le \|\mathrm{Var}(\nabla\ell)\|_1/n$
-- statement:
--   Let $(Z,P)$ be a probability space, $w\in\mathbb R^m$, and $\nabla\ell(w;\cdot):Z\to\mathbb R^m$ a function with finite second moment under $P$. For a sample size $n\ge1$ draw a batch $b=(b_1,\dots,b_n)$ of $n$ independent points with law $P$ and let $g=\frac1n\sum_{i=1}^n\nabla\ell(w;b_i)$. Then
--
--   $$
--   \|\mathrm{Var}(g)\|_1\;\le\;\frac{\|\mathrm{Var}(\nabla\ell(w;\cdot))\|_1}{n},
--   $$
--
--   where for a random vector $X$, $\|\mathrm{Var}(X)\|_1=\mathbb E\|X-\mathbb EX\|^2$ is the sum of its componentwise variances.
--
--   This is the bound the paper reads off (3.5) on p. 12; it is what makes the noise term of the one-step estimate decay like $1/n_k$.
--
--   **Formalization Note** The paper's middle expression carries the finite-population factor $(N-n_k)/(N-1)$ of sampling without replacement from $N$ points. The formalization samples with replacement (i.i.d. from $P$), the limit $N\to\infty$ the paper takes on p. 5; for i.i.d. sampling the inequality holds with equality, and the inequality is what the proof uses.
-- source:
--   Byrd, Chin, Nocedal, Wu, Sample size selection in optimization methods for machine learning, Math. Program. (2012), doi:10.1007/s10107-012-0572-5 — authors' version of 18 Oct 2011, p. 12, unnumbered display after 'From (3.5), we note that'

import Mathlib
import Definitions.Def_DynSampleSize_Stoch_Model

open MeasureTheory

namespace DynSampleSize.Stoch

/-- §4.2, p. 12 (display after "From (3.5), we note that"): for a batch `b` of `n ≥ 1` i.i.d. draws
from `P`, the variance of the batch gradient is at most the per-sample gradient variance over `n`,
`‖Var(g)‖₁ ≤ ‖Var(∇ℓ(w; i))‖₁ / n`. -/
theorem sample_mean_variance {m : ℕ} {Z : Type*} [MeasurableSpace Z] (P : Measure Z)
    [IsProbabilityMeasure P]
    (gradℓ : EuclideanSpace ℝ (Fin m) → Z → EuclideanSpace ℝ (Fin m))
    (w : EuclideanSpace ℝ (Fin m)) (hgrad : MemLp (gradℓ w) 2 P) (n : ℕ) (hn : 1 ≤ n) :
    vecVar (Measure.pi (fun _ : Fin n => P)) (batchGrad gradℓ n w) ≤
      vecVar P (gradℓ w) / n := by sorry

end DynSampleSize.Stoch
