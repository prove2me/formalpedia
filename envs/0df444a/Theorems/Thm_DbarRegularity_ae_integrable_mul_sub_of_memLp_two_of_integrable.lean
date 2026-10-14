-- Prove2me | Theorems.Thm_DbarRegularity_ae_integrable_mul_sub_of_memLp_two_of_integrable
-- name    : DbarRegularity.ae_integrable_mul_sub_of_memLp_two_of_integrable
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T15:24:35.4597+00:00
-- url     : https://prove2.me/theorems/e963554f-4769-4bdf-a781-3622a048e623
-- title:
--   For $K\in L^2$ and $f\in L^1$ on $\mathbb R^d$, $y\mapsto K(x-y)f(y)$ is integrable for a.e. $x$
-- statement:
--   Let $d\ge0$, $K\in L^2(\mathbb R^d)$ and $f\in L^1(\mathbb R^d)$, both complex valued. Then for almost every $x\in\mathbb R^d$ the function
--   $$y\;\longmapsto\;K(x-y)\,f(y)$$
--   is Lebesgue integrable on $\mathbb R^d$.
--
--   So the convolution $K*f(x)=\int K(x-y)f(y)\,dy$ is given by an absolutely convergent integral at almost every point; in particular $f\mapsto K*f$ is additive almost everywhere on $L^1$.
--
--   **Formalization Note.** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` with Lebesgue measure `volume`. $L^2$ and $L^1$ membership are `MemLp K 2 volume` and `Integrable f volume`; the conclusion is `∀ᵐ x, Integrable (fun y => K (x - y) * f y) volume`.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton University Press (1970), Chapter II, § 2.2, pp. 29–31

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace DbarRegularity

open MeasureTheory
open scoped ENNReal

/-- For `K ∈ L²(ℝ^d)` and `f ∈ L¹(ℝ^d)`, the integrand `y ↦ K(x - y) f(y)` is integrable for almost
every `x`. -/
theorem ae_integrable_mul_sub_of_memLp_two_of_integrable {d : ℕ}
    {K f : EuclideanSpace ℝ (Fin d) → ℂ} (hK : MemLp K 2 volume) (hf : Integrable f volume) :
    ∀ᵐ x, Integrable (fun y => K (x - y) * f y) volume := by sorry

end DbarRegularity
