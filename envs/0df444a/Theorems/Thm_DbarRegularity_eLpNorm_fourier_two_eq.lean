-- Prove2me | Theorems.Thm_DbarRegularity_eLpNorm_fourier_two_eq
-- name    : DbarRegularity.eLpNorm_fourier_two_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T15:16:25.164986+00:00
-- url     : https://prove2.me/theorems/86a8d48e-e104-493c-bbc6-f7a535068924
-- title:
--   Plancherel identity $\|\hat g\|_{2}=\|g\|_{2}$ for $g\in L^1\cap L^2(\mathbb R^d)$
-- statement:
--   Let $d\ge0$ and let $g:\mathbb R^d\to\mathbb C$ be integrable and square integrable. Then its Fourier integral $\hat g(\xi)=\int e^{-2\pi i\langle x,\xi\rangle}g(x)\,dx$ satisfies
--   $$\|\hat g\|_{L^2(\mathbb R^d)}=\|g\|_{L^2(\mathbb R^d)} .$$
--
--   This is Plancherel's identity for the classical Fourier integral on $L^1\cap L^2$.
--
--   **Formalization Note.** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` with Lebesgue measure `volume`. $\hat g$ is Mathlib's Fourier integral `𝓕 g`, and both norms are `eLpNorm · 2 volume` in `ℝ≥0∞`.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton University Press (1970), Chapter II, § 2.2, p. 29

import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace DbarRegularity

open MeasureTheory FourierTransform
open scoped ENNReal

/-- Plancherel on `L¹ ∩ L²` for the Fourier integral. -/
theorem eLpNorm_fourier_two_eq {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → ℂ) (hg1 : Integrable g volume)
    (hg2 : MemLp g 2 volume) : eLpNorm (𝓕 g) 2 volume = eLpNorm g 2 volume := by sorry

end DbarRegularity
