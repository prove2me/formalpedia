-- Prove2me | Theorems.Thm_FiniteEnergyPlane_expDecayCInfty_symm_div_sub
-- name    : FiniteEnergyPlane.expDecayCInfty_symm_div_sub
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-16T22:20:17.817454+00:00
-- url     : https://prove2.me/theorems/59841655-382e-4e65-85a4-cb416520db14
-- title:
--   Exponential asymptotics at infinity pass to the inverse of a smooth homeomorphism of the plane
-- statement:
--   Let $\psi : \mathbb{C} \to \mathbb{C}$ be a homeomorphism such that $\psi$ and $\psi^{-1}$ are $C^\infty$, and let $\kappa \ne 0$, $b > 0$. Suppose that $\psi(z)/z - \kappa$ decays like $e^{-bs}$ in $C^\infty$ in the cylindrical coordinates $z = e^{2\pi(s+it)}$ at $\infty$. Then $\psi^{-1}(z)/z - \kappa^{-1}$ decays like $e^{-bs}$ in $C^\infty$ in the same coordinates.
--
--   Role: a reparametrization of the plane that is asymptotic to the complex dilation by $\kappa$ at $\infty$ has an inverse asymptotic to the dilation by $\kappa^{-1}$, with the same exponential rate, so asymptotic statements can be transported in both directions.
--
--   Formalization Note: $e^{2\pi(s+it)}$ is `cylInf s t`; decay is `ExpDecayCInfty`.
-- source:
--   Standard calculus of exponential decay on cylindrical ends; used toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 6

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open Metric
open scoped ContDiff Real

/-- Asymptotics of the inverse. If `ψ` is a homeomorphism of `ℂ`, smooth with smooth inverse,
and `ψ(z)/z - κ` decays like `e^{-bs}` in `C^∞` in the cylindrical coordinates `z = e^{2π(s+it)}`,
with `κ ≠ 0` and `b > 0`, then `ψ⁻¹(z)/z - κ⁻¹` decays like `e^{-bs}` in `C^∞`. -/
theorem expDecayCInfty_symm_div_sub (ψ : ℂ ≃ₜ ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hψ' : ContDiff ℝ ∞ ψ.symm) (κ : ℂ) (hκ : κ ≠ 0) (b : ℝ) (hb : 0 < b)
    (has : ExpDecayCInfty (fun p : ℝ × ℝ => ψ (cylInf p.1 p.2) / cylInf p.1 p.2 - κ) b) :
    ExpDecayCInfty (fun p : ℝ × ℝ => ψ.symm (cylInf p.1 p.2) / cylInf p.1 p.2 - κ⁻¹) b := by
  sorry

end FiniteEnergyPlane
