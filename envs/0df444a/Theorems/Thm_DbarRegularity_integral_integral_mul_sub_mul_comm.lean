-- Prove2me | Theorems.Thm_DbarRegularity_integral_integral_mul_sub_mul_comm
-- name    : DbarRegularity.integral_integral_mul_sub_mul_comm
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T16:53:11.302621+00:00
-- url     : https://prove2.me/theorems/d87ca7e2-1dc0-4e1d-b9d1-972c8bb89ad1
-- title:
--   Transpose of convolution with an $L^2$ kernel on $\mathbb R^d$: $\int (K*f)\,g=\int\big(\int K(x-y)g(x)\,dx\big)f(y)\,dy$
-- statement:
--   Let $d\ge0$, let $K,g\in L^2(\mathbb R^d)$ and $f\in L^1(\mathbb R^d)$, all complex valued. Then
--   $$\int_{\mathbb R^d}\Big(\int_{\mathbb R^d}K(x-y)\,f(y)\,dy\Big)\,g(x)\,dx\;=\;\int_{\mathbb R^d}\Big(\int_{\mathbb R^d}K(x-y)\,g(x)\,dx\Big)\,f(y)\,dy .$$
--
--   So the transpose of convolution with $K$, with respect to the bilinear pairing $\int uv$, is convolution with the reflected kernel $x\mapsto K(-x)$.
--
--   **Formalization Note.** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` with Lebesgue measure `volume`. The hypotheses are `MemLp K 2 volume`, `Integrable f volume` and `MemLp g 2 volume`. All integrals are Bochner integrals.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton University Press (1970), Chapter II, § 2.2, p. 31

import Definitions.Def_DbarRegularity_Setting
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace DbarRegularity

open MeasureTheory
open scoped ENNReal

/-- For `K, g ∈ L²(ℝ^d)` and `f ∈ L¹(ℝ^d)`:
`∫ (∫ K(x - y) f(y) dy) g(x) dx = ∫ (∫ K(x - y) g(x) dx) f(y) dy`. -/
theorem integral_integral_mul_sub_mul_comm {d : ℕ} {K f g : EuclideanSpace ℝ (Fin d) → ℂ}
    (hK : MemLp K 2 volume) (hf : Integrable f volume) (hg : MemLp g 2 volume) :
    ∫ x, (∫ y, K (x - y) * f y) * g x = ∫ y, (∫ x, K (x - y) * g x) * f y := by sorry

end DbarRegularity
