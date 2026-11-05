-- Prove2me | Theorems.Thm_FiniteEnergyPlane_setIntegral_ball_omega0_fderiv_eq
-- name    : FiniteEnergyPlane.setIntegral_ball_omega0_fderiv_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T18:14:26.445031+00:00
-- url     : https://prove2.me/theorems/f4b87472-a4fb-4a1e-b2ee-b808f46522dc
-- title:
--   Stokes' formula on a disc for the pullback of the standard symplectic form
-- statement:
--   Let $w : \mathbb{C} \to \mathbb{R}^{2n+2}$ be a smooth map, $\omega_0$ the standard symplectic form, and $R > 0$. Then
--   $$\int_{B_R(0)} \omega_0(\partial_s w, \partial_t w)\, ds\, dt = \frac{1}{2} \int_0^{2\pi} \omega_0\big(w(Re^{i\theta}),\, \partial_\theta\, w(Re^{i\theta})\big)\, d\theta.$$
--
--   This expresses the $\omega_0$-area of a disc as the action of its boundary loop, with no further hypothesis on $w$. It applies in particular to rescaled maps $\chi(a)\, w$ arising in energy computations for finite-energy curves.
--
--   Formalization Note: $\partial_\theta w(Re^{i\theta}) = Dw(Re^{i\theta})[Re^{i\theta} \cdot i]$ and $\partial_s w = Dw[1]$, $\partial_t w = Dw[i]$, with `circleMap 0 R θ` $= Re^{i\theta}$.
-- source:
--   Standard (Stokes' theorem); used as in H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515-563, p. 537

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Stokes' formula on a disc for the pullback of the standard symplectic form. For a smooth map
`w : ℂ → V n`, the integral of `ω₀(∂ₛw, ∂ₜw)` over `B(0, R)` equals
`(1/2) ∫₀^{2π} ω₀(w, ∂_θ w) dθ` on the boundary circle of radius `R`. -/
theorem setIntegral_ball_omega0_fderiv_eq {n : ℕ} (w : ℂ → V n) (hw : ContDiff ℝ ∞ w) (R : ℝ)
    (hR : 0 < R) :
    ∫ z in ball 0 R, omega0 (fderiv ℝ w z 1) (fderiv ℝ w z Complex.I) =
      (1 / 2) * ∫ θ in (0 : ℝ)..2 * π, omega0 (w (circleMap 0 R θ))
        (fderiv ℝ w (circleMap 0 R θ) (circleMap 0 R θ * Complex.I)) := by
  sorry

end FiniteEnergyPlane
