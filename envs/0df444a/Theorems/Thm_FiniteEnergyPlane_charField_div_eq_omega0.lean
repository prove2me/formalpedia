-- Prove2me | Theorems.Thm_FiniteEnergyPlane_charField_div_eq_omega0
-- name    : FiniteEnergyPlane.charField_div_eq_omega0
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-26T21:20:48.212463+00:00
-- url     : https://prove2.me/theorems/a711871d-544c-5155-8a3e-61d375c50f8c
-- title:
--   Divergence of the characteristic field of a disk
-- statement:
--   Let $e : \mathbb{C} \to V_1 = \mathbb{R}^4$ be smooth and let $V = \mathtt{charField}\ e$ be its characteristic field on the parameter plane, i.e. $(ds\wedge dt)(V, w) = \lambda_0(e(z))(De(z) w)$. Then the divergence of $V$ is the $d\lambda_0$-area density of $e$:
--   $$\operatorname{Re}(DV(z)\cdot 1) + \operatorname{Im}(DV(z) \cdot i) = \omega_0(\partial_s e(z), \partial_t e(z)).$$
--
--   Role: identifies the source term of the characteristic flow with the integrand of the positive $d\lambda_0$-area `diskArea`.
-- source:
--   Elementary lemma in the setting of U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), § 3.2

import Definitions.Def_FiniteEnergyPlane_SpanningDisk

namespace FiniteEnergyPlane

open scoped ContDiff

/-- The divergence of the characteristic field of a smooth disk `e : ℂ → V 1` is the `dλ₀`-area
density of `e`: `(DV · 1).re + (DV · i).im = ω₀(∂ₛe, ∂ₜe)` for `V = charField e`. -/
theorem charField_div_eq_omega0 (e : ℂ → V 1) (he : ContDiff ℝ ∞ e) (z : ℂ) :
    (fderiv ℝ (charField e) z 1).re + (fderiv ℝ (charField e) z Complex.I).im =
      omega0 (ds e z) (dt e z) := by
  sorry

end FiniteEnergyPlane
