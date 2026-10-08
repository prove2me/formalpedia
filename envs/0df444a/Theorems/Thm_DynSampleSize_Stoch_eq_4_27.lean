-- Prove2me | Theorems.Thm_DynSampleSize_Stoch_eq_4_27
-- name    : DynSampleSize.Stoch.eq_4_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:28:28.531924+00:00
-- url     : https://prove2.me/theorems/57bdf5e4-4795-44ed-8d19-c8c2595e07f1
-- title:
--   (4.27) — one-step recursion $E[J(w_{k+1})-J(w^*)] \le (1-\lambda/(2L))(J(w_k)-J(w^*)) + \omega/(2Ln_k)$
-- statement:
--   Under the stochastic model of §4.2 and (4.2) with constants $0<\lambda<L$, let $w^*$ minimize $J$ and let $\omega$ bound the gradient variance uniformly (4.22):
--   $$\|\mathrm{Var}(\nabla\ell(w;\cdot))\|_1\le\omega\qquad\text{for all } w .$$
--   Fix a point $w$ and a sample size $n\ge1$, draw a batch of $n$ independent points with law $P$, and let $g$ be its batch gradient at $w$. Then $J(w-g/L)$ is integrable and
--
--   $$
--   \mathbb E\big[J(w-\tfrac1L g)-J(w^*)\big]\;\le\;\Big(1-\frac{\lambda}{2L}\Big)\big(J(w)-J(w^*)\big)+\frac{\omega}{2Ln}.
--   $$
--
--   With $w=w_k$ and $n=n_k$ this is the conditional one-step recursion from which Theorem 4.2 follows by induction on $k$.
-- source:
--   Byrd, Chin, Nocedal, Wu, Sample size selection in optimization methods for machine learning, Math. Program. (2012), doi:10.1007/s10107-012-0572-5 — authors' version of 18 Oct 2011, p. 12, (4.27); p. 11, (4.22)

import Mathlib
import Definitions.Def_DynSampleSize_Stoch_UniformConvexity
import Definitions.Def_DynSampleSize_Stoch_Model

open MeasureTheory

namespace DynSampleSize.Stoch

/-- (4.27), p. 12: under (4.22) (`‖Var(∇ℓ(w; ·))‖₁ ≤ ω` for every `w`), at a point `w`, with the batch
`b` of `n ≥ 1` i.i.d. draws from `P`,
`E[J(w − g/L) − J(w*)] ≤ (1 − λ/(2L)) (J(w) − J(w*)) + ω/(2Ln)`, and the expectation exists. -/
theorem eq_4_27 {m : ℕ} {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (ℓ : EuclideanSpace ℝ (Fin m) → Z → ℝ)
    (gradℓ : EuclideanSpace ℝ (Fin m) → Z → EuclideanSpace ℝ (Fin m))
    (hmodel : StochModel P ℓ gradℓ) (lam L : ℝ) (hJ : UniformlyConvex (objective P ℓ) lam L)
    (wstar : EuclideanSpace ℝ (Fin m)) (hwstar : ∀ w, objective P ℓ wstar ≤ objective P ℓ w)
    (ω : ℝ) (hω : ∀ w, vecVar P (gradℓ w) ≤ ω)
    (w : EuclideanSpace ℝ (Fin m)) (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun b => objective P ℓ (w - (1 / L) • batchGrad gradℓ n w b))
        (Measure.pi (fun _ : Fin n => P)) ∧
      ∫ b, (objective P ℓ (w - (1 / L) • batchGrad gradℓ n w b) - objective P ℓ wstar)
          ∂(Measure.pi (fun _ : Fin n => P)) ≤
        (1 - lam / (2 * L)) * (objective P ℓ w - objective P ℓ wstar) + ω / (2 * L * n) := by sorry

end DynSampleSize.Stoch
