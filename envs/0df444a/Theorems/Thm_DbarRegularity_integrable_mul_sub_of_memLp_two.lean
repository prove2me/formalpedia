-- Prove2me | Theorems.Thm_DbarRegularity_integrable_mul_sub_of_memLp_two
-- name    : DbarRegularity.integrable_mul_sub_of_memLp_two
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T15:19:16.9853+00:00
-- url     : https://prove2.me/theorems/aab2d708-f395-428e-bc9b-86dec8417c3b
-- title:
--   For $K,f\in L^2(\mathbb R^d)$ the function $y\mapsto K(x-y)f(y)$ is integrable for every $x$
-- statement:
--   Let $d\ge0$ and let $K,f\in L^2(\mathbb R^d)$ be complex valued. Then for every $x\in\mathbb R^d$ the function
--   $$y\;\longmapsto\;K(x-y)\,f(y)$$
--   is Lebesgue integrable on $\mathbb R^d$.
--
--   Consequently the convolution $K*f(x)=\int K(x-y)f(y)\,dy$ of two square-integrable functions is defined at every point, not only almost everywhere.
--
--   **Formalization Note.** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` with Lebesgue measure `volume`. $L^2$ membership is `MemLp · 2 volume`; integrability is `Integrable · volume`.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton University Press (1970), Chapter II, § 2.2, p. 29

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace DbarRegularity

open MeasureTheory
open scoped ENNReal

/-- Integrability of `y ↦ K (x - y) * f y` for `K, f ∈ L²`. -/
theorem integrable_mul_sub_of_memLp_two {d : ℕ} {K f : EuclideanSpace ℝ (Fin d) → ℂ}
    (hK : MemLp K 2 volume) (hf : MemLp f 2 volume) (x : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun y => K (x - y) * f y) volume := by sorry

end DbarRegularity
