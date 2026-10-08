-- Prove2me | Theorems.Thm_DynSampleSize_Stoch_eq_4_26
-- name    : DynSampleSize.Stoch.eq_4_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:28:44.551596+00:00
-- url     : https://prove2.me/theorems/b8ae4d23-6e7e-49b0-a038-45595809fd03
-- title:
--   (4.26) — conditional expected decrease of one dynamic batch step
-- statement:
--   Under the stochastic model of §4.2 and (4.2) with constants $0<\lambda<L$, fix a point $w$ and a sample size $n\ge1$, draw a batch of $n$ independent points with law $P$, and let $g$ be its batch gradient at $w$. Then $J(w-g/L)$ is integrable and
--
--   $$
--   \mathbb E\big[J(w-\tfrac1L g)\big]\;\le\;J(w)-\frac1{2L}\|\nabla J(w)\|^2+\frac1{2Ln}\,\|\mathrm{Var}(\nabla\ell(w;\cdot))\|_1 .
--   $$
--
--   With $w=w_k$ and $n=n_k$ this is the paper's conditional expectation of $J(w_{k+1})$ given $w_k$: a deterministic gradient step's decrease, minus a noise term that shrinks with the batch size.
-- source:
--   Byrd, Chin, Nocedal, Wu, Sample size selection in optimization methods for machine learning, Math. Program. (2012), doi:10.1007/s10107-012-0572-5 — authors' version of 18 Oct 2011, p. 12, (4.26)

import Mathlib
import Definitions.Def_DynSampleSize_Stoch_UniformConvexity
import Definitions.Def_DynSampleSize_Stoch_Model

open MeasureTheory

namespace DynSampleSize.Stoch

/-- (4.26), p. 12: at a point `w`, with the batch `b` of `n ≥ 1` i.i.d. draws from `P`,
`E[J(w − g/L)] ≤ J(w) − (1/(2L))‖∇J(w)‖² + (1/(2Ln)) ‖Var(∇ℓ(w; ·))‖₁`, and the expectation exists. -/
theorem eq_4_26 {m : ℕ} {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (ℓ : EuclideanSpace ℝ (Fin m) → Z → ℝ)
    (gradℓ : EuclideanSpace ℝ (Fin m) → Z → EuclideanSpace ℝ (Fin m))
    (hmodel : StochModel P ℓ gradℓ) (lam L : ℝ) (hJ : UniformlyConvex (objective P ℓ) lam L)
    (w : EuclideanSpace ℝ (Fin m)) (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun b => objective P ℓ (w - (1 / L) • batchGrad gradℓ n w b))
        (Measure.pi (fun _ : Fin n => P)) ∧
      ∫ b, objective P ℓ (w - (1 / L) • batchGrad gradℓ n w b) ∂(Measure.pi (fun _ : Fin n => P)) ≤
        objective P ℓ w - 1 / (2 * L) * ‖gradient (objective P ℓ) w‖ ^ 2 +
          1 / (2 * L * n) * vecVar P (gradℓ w) := by sorry

end DynSampleSize.Stoch
