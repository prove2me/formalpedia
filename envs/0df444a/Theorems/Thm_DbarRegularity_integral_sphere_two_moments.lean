-- Prove2me | Theorems.Thm_DbarRegularity_integral_sphere_two_moments
-- name    : DbarRegularity.integral_sphere_two_moments
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T20:34:44.572769+00:00
-- url     : https://prove2.me/theorems/8217ca6d-c44c-4634-96a0-7ddc9e00633f
-- title:
--   First and second moments of the surface measure on the unit circle
-- statement:
--   Let $\sigma$ be the surface (arc-length) measure on the unit circle $S^1\subset\mathbb R^2$. Then for $i,j\in\{0,1\}$
--   $$\int_{S^1}\omega_i\,d\sigma(\omega)=0,\qquad \int_{S^1}\omega_i\,\omega_j\,d\sigma(\omega)=\pi\,\delta_{ij}.$$
--
--   **Formalization Note.** $\mathbb R^2$ is `EuclideanSpace ℝ (Fin 2)`, the circle is `sphere (0 : EuclideanSpace ℝ (Fin 2)) 1` as a subtype and $\sigma$ is Mathlib's `volume.toSphere`; $\omega_i$ is the coordinate `ω.1 i`, and $\pi\delta_{ij}$ is `if i = j then Real.pi else 0`.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter III, § 1.3, Proposition 4, p. 60

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace DbarRegularity

open MeasureTheory Metric Set

/-- First and second moments of the arc-length measure on the unit circle of `ℝ²`:
`∫ ωᵢ dσ = 0` and `∫ ωᵢ ωⱼ dσ = π δᵢⱼ`. -/
theorem integral_sphere_two_moments :
    (∀ i : Fin 2, ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, ω.1 i ∂volume.toSphere = 0) ∧
    (∀ i j : Fin 2, ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, ω.1 i * ω.1 j
      ∂volume.toSphere = if i = j then Real.pi else 0) := by sorry

end DbarRegularity
