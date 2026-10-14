-- Prove2me | Theorems.Thm_DbarRegularity_eLpNorm_integral_mul_sub_le
-- name    : DbarRegularity.eLpNorm_integral_mul_sub_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T15:03:07.346399+00:00
-- url     : https://prove2.me/theorems/8fd824ac-1a95-44f4-af4e-364439eebbfe
-- title:
--   Young's inequality $\|h*f\|_{L^2}\le\|h\|_{L^2}\|f\|_{L^1}$ for the pointwise convolution integral on $\mathbb R^d$
-- statement:
--   Let $d\ge0$ and let $h,f:\mathbb R^d\to\mathbb C$ be almost-everywhere strongly measurable. Then
--   $$\Big\|\,x\mapsto\int_{\mathbb R^d}h(x-y)\,f(y)\,dy\,\Big\|_{L^2(\mathbb R^d)}\;\le\;\|h\|_{L^2(\mathbb R^d)}\,\|f\|_{L^1(\mathbb R^d)} .$$
--
--   This is Young's convolution inequality for $L^2\times L^1\to L^2$, for the convolution defined pointwise by the Bochner integral. In particular, convolution with a fixed $f\in L^1$ is a bounded operator on $L^2$ with norm at most $\|f\|_1$, and the bound holds with no finiteness assumptions (both sides may be infinite).
--
--   **Formalization Note.** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` with Lebesgue measure. The norms are `eLpNorm · 2 volume` and `eLpNorm · 1 volume` in `ℝ≥0∞`; the integral is the Bochner integral `∫ y, h (x - y) * f y`, set to $0$ where the integrand is not integrable.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton University Press (1970), Chapter II, § 2.2, p. 29

import Theorems.Thm_DbarRegularity_lintegral_sq_lintegral_mul_le
import Mathlib.MeasureTheory.Integral.Prod

namespace DbarRegularity

open MeasureTheory
open scoped ENNReal

/-- `‖∫ h(· - y) f(y) dy‖_{L²} ≤ ‖h‖_{L²} ‖f‖_{L¹}`. -/
theorem eLpNorm_integral_mul_sub_le {d : ℕ} (h f : EuclideanSpace ℝ (Fin d) → ℂ)
    (hh : AEStronglyMeasurable h volume) (hf : AEStronglyMeasurable f volume) :
    eLpNorm (fun x => ∫ y, h (x - y) * f y) 2 volume ≤ eLpNorm h 2 volume * eLpNorm f 1 volume := by sorry

end DbarRegularity
