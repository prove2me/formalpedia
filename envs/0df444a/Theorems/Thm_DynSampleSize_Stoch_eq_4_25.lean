-- Prove2me | Theorems.Thm_DynSampleSize_Stoch_eq_4_25
-- name    : DynSampleSize.Stoch.eq_4_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:29:39.789371+00:00
-- url     : https://prove2.me/theorems/f08c9e1b-652c-4767-94b9-54745e8c6d39
-- title:
--   (4.25) — expected value after one dynamic batch step in terms of $E\|g\|^2 = \|\nabla J\|^2 + \|\mathrm{Var}(g)\|_1$
-- statement:
--   Let $(Z,P)$, $\ell$, $\nabla\ell$ and $J(w)=\int\ell(w;z)\,dP(z)$ satisfy the stochastic model of §4.2 (integrable loss, measurable gradient with finite second moment, $\nabla J(w)=\int\nabla\ell(w;z)\,dP(z)$), and let $J$ satisfy (4.2) with constants $0<\lambda<L$. Fix a point $w$ and a sample size $n\ge1$, draw a batch $b=(b_1,\dots,b_n)$ of $n$ independent points with law $P$, and let $g=\frac1n\sum_i\nabla\ell(w;b_i)$. Then $J(w-g/L)$ and $\|g\|^2$ are integrable, and
--
--   $$
--   \begin{aligned}
--   \mathbb E[J(w-\tfrac1L g)] &\le J(w)-\frac1L\|\nabla J(w)\|^2+\frac1{2L}\mathbb E[\|g\|^2]\\
--   \mathbb E[\|g\|^2] &= \|\nabla J(w)\|^2+\|\mathrm{Var}(g)\|_1 ,
--   \end{aligned}
--   $$
--
--   where $\|\mathrm{Var}(g)\|_1=\mathbb E\|g-\mathbb E g\|^2$.
--
--   In the paper, $w=w_k$ is the current iterate and the expectation is conditional on $w_k$; this is the first step of the one-iteration analysis of the dynamic batch method.
--
--   **Formalization Note** The batch law is the product measure $P^{\otimes n}$ on $Z^n$; fixing $w$ and averaging over the batch is exactly the paper's conditional expectation given $w_k$.
-- source:
--   Byrd, Chin, Nocedal, Wu, Sample size selection in optimization methods for machine learning, Math. Program. (2012), doi:10.1007/s10107-012-0572-5 — authors' version of 18 Oct 2011, p. 11, (4.25)

import Mathlib
import Definitions.Def_DynSampleSize_Stoch_UniformConvexity
import Definitions.Def_DynSampleSize_Stoch_Model

open MeasureTheory

namespace DynSampleSize.Stoch

/-- (4.25), p. 11: at a point `w`, with the batch `b` of `n ≥ 1` i.i.d. draws from `P` and
`g = batchGrad gradℓ n w b`, the step `w − g/L` satisfies
`E[J(w − g/L)] ≤ J(w) − (1/L)‖∇J(w)‖² + (1/(2L)) E‖g‖²` and
`E‖g‖² = ‖∇J(w)‖² + ‖Var(g)‖₁`; all expectations exist. -/
theorem eq_4_25 {m : ℕ} {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (ℓ : EuclideanSpace ℝ (Fin m) → Z → ℝ)
    (gradℓ : EuclideanSpace ℝ (Fin m) → Z → EuclideanSpace ℝ (Fin m))
    (hmodel : StochModel P ℓ gradℓ) (lam L : ℝ) (hJ : UniformlyConvex (objective P ℓ) lam L)
    (w : EuclideanSpace ℝ (Fin m)) (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun b => objective P ℓ (w - (1 / L) • batchGrad gradℓ n w b))
        (Measure.pi (fun _ : Fin n => P)) ∧
      Integrable (fun b => ‖batchGrad gradℓ n w b‖ ^ 2) (Measure.pi (fun _ : Fin n => P)) ∧
      ∫ b, objective P ℓ (w - (1 / L) • batchGrad gradℓ n w b) ∂(Measure.pi (fun _ : Fin n => P)) ≤
        objective P ℓ w - 1 / L * ‖gradient (objective P ℓ) w‖ ^ 2 +
          1 / (2 * L) * ∫ b, ‖batchGrad gradℓ n w b‖ ^ 2 ∂(Measure.pi (fun _ : Fin n => P)) ∧
      ∫ b, ‖batchGrad gradℓ n w b‖ ^ 2 ∂(Measure.pi (fun _ : Fin n => P)) =
        ‖gradient (objective P ℓ) w‖ ^ 2 +
          vecVar (Measure.pi (fun _ : Fin n => P)) (batchGrad gradℓ n w) := by sorry

end DynSampleSize.Stoch
