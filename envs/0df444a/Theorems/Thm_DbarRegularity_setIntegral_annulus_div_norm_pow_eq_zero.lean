-- Prove2me | Theorems.Thm_DbarRegularity_setIntegral_annulus_div_norm_pow_eq_zero
-- name    : DbarRegularity.setIntegral_annulus_div_norm_pow_eq_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T19:17:21.975977+00:00
-- url     : https://prove2.me/theorems/c2fb1a1e-9a23-443f-9922-c42798803551
-- title:
--   Homogeneous kernels with spherical mean zero integrate to zero on annuli
-- statement:
--   Let $d\ge0$ and let $\Omega:\mathbb{R}^d\to\mathbb{C}$ be homogeneous of degree $0$, i.e. $\Omega(tx)=\Omega(x)$ for all $x$ and all $t>0$, with mean zero on the unit sphere: $\int_{S^{d-1}}\Omega\,d\sigma=0$. Then for all $0<R_1$ and all $R_2$
--   $$\int_{R_1<|x|<R_2}\frac{\Omega(x)}{|x|^d}\,dx=0 .$$
--
--   **Formalization Note.** $\mathbb{R}^d$ is `EuclideanSpace ℝ (Fin d)` with `volume`; $\sigma$ is Mathlib's `volume.toSphere` on `sphere 0 1`. The integrals are Bochner integrals, so no measurability or integrability of $\Omega$ is assumed (a non-integrable integrand has Bochner integral $0$). $|x|^d$ is the real power `‖x‖ ^ d` cast to `ℂ`.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter II, § 4.2, Theorem 3, p. 39

import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace DbarRegularity

open MeasureTheory Set Metric
open scoped ENNReal

/-- If `Ω` on `ℝ^d` is homogeneous of degree `0` and has mean zero on the unit sphere, then
`Ω(x) / |x|^d` has integral zero over every annulus `{R₁ < |x| < R₂}`. -/
theorem setIntegral_annulus_div_norm_pow_eq_zero {d : ℕ} (Ω : EuclideanSpace ℝ (Fin d) → ℂ)
    (hhom : ∀ x, ∀ t : ℝ, 0 < t → Ω (t • x) = Ω x)
    (hmean : ∫ x : sphere (0 : EuclideanSpace ℝ (Fin d)) 1, Ω x ∂(volume.toSphere) = 0)
    (R₁ R₂ : ℝ) (hR₁ : 0 < R₁) :
    ∫ x in {x : EuclideanSpace ℝ (Fin d) | R₁ < ‖x‖ ∧ ‖x‖ < R₂},
      Ω x / ((‖x‖ ^ d : ℝ) : ℂ) = 0 := by sorry

end DbarRegularity
