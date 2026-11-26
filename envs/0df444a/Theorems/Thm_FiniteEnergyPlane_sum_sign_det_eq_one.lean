-- Prove2me | Theorems.Thm_FiniteEnergyPlane_sum_sign_det_eq_one
-- name    : FiniteEnergyPlane.sum_sign_det_eq_one
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-25T23:07:36.836194+00:00
-- url     : https://prove2.me/theorems/369a00a4-7726-5a5c-86f0-081a90e01082
-- title:
--   Index sum of an outward pointing planar vector field
-- statement:
--   Let $V:\mathbb{C}\to\mathbb{C}$ be a smooth vector field with
--   $$\langle z,V(z)\rangle>0\qquad\text{for }|z|=1,$$
--   whose zeros in the closed unit disk form a finite set $Z$ and are nondegenerate. Then
--   $$\sum_{z\in Z}\operatorname{sign}\det DV(z)=1 .$$
--
--   The formula is a statement on planar vector fields, independent of contact geometry.
--
--   **Formalization Note** The determinant is that of the real derivative. In the source $V$ is the field of the characteristic foliation of a disk with transverse boundary.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, A characterization of the tight 3-sphere II, Comm. Pure Appl. Math. 52 (1999), 1139–1177, formula (3.1)

import Definitions.Def_FiniteEnergyPlane_DiskFoliation

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

/-- Hofer–Wysocki–Zehnder (1999, tight sphere II), (3.1). A smooth vector field on the plane that points out of
the unit disk along the unit circle and whose zeros in the disk are nondegenerate has index sum `1`. -/
theorem sum_sign_det_eq_one (V : ℂ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hout : ∀ z ∈ sphere (0 : ℂ) 1, 0 < z.re * (V z).re + z.im * (V z).im) (Z : Finset ℂ)
    (hZ : ∀ z ∈ closedBall (0 : ℂ) 1, V z = 0 ↔ z ∈ Z) (hZ' : (Z : Set ℂ) ⊆ closedBall 0 1)
    (hdet : ∀ z ∈ Z, LinearMap.det (fderiv ℝ V z : ℂ →ₗ[ℝ] ℂ) ≠ 0) :
    ∑ z ∈ Z, ((SignType.sign (LinearMap.det (fderiv ℝ V z : ℂ →ₗ[ℝ] ℂ)) : SignType) : ℤ) = 1 := by
  sorry

end FiniteEnergyPlane
