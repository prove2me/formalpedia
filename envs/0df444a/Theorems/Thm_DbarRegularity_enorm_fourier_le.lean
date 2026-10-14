-- Prove2me | Theorems.Thm_DbarRegularity_enorm_fourier_le
-- name    : DbarRegularity.enorm_fourier_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T15:22:00.681804+00:00
-- url     : https://prove2.me/theorems/9c566371-43de-443f-8559-ca8de5cafe38
-- title:
--   $|\hat f(\xi)|\le\|f\|_{L^1}$ for integrable $f$ on $\mathbb R^d$
-- statement:
--   Let $d\ge0$ and let $f:\mathbb R^d\to\mathbb C$ be integrable. Then for every $\xi\in\mathbb R^d$ the Fourier integral satisfies
--   $$|\hat f(\xi)|=\Big|\int_{\mathbb R^d}e^{-2\pi i\langle x,\xi\rangle}f(x)\,dx\Big|\;\le\;\|f\|_{L^1(\mathbb R^d)} .$$
--
--   This is the uniform bound $\|\hat f\|_\infty\le\|f\|_1$ for the Fourier transform of an integrable function.
--
--   **Formalization Note.** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` with Lebesgue measure `volume`. $\hat f$ is Mathlib's `𝓕 f`; the bound is stated in `ℝ≥0∞` as `‖𝓕 f ξ‖ₑ ≤ eLpNorm f 1 volume`.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton University Press (1970), Chapter II, § 2.2, p. 29

import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace DbarRegularity

open MeasureTheory FourierTransform
open scoped ENNReal

/-- `‖𝓕 f‖_∞ ≤ ‖f‖₁`, pointwise. -/
theorem enorm_fourier_le {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℂ) (hf : Integrable f volume)
    (ξ : EuclideanSpace ℝ (Fin d)) : ‖𝓕 f ξ‖ₑ ≤ eLpNorm f 1 volume := by sorry

end DbarRegularity
