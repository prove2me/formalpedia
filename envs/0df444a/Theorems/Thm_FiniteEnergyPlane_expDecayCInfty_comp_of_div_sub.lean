-- Prove2me | Theorems.Thm_FiniteEnergyPlane_expDecayCInfty_comp_of_div_sub
-- name    : FiniteEnergyPlane.expDecayCInfty_comp_of_div_sub
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-16T21:57:07.824161+00:00
-- url     : https://prove2.me/theorems/75e6cd2a-20a4-43cd-a15c-5878a255dedc
-- title:
--   Exponential decay at infinity is preserved by composition with a map asymptotic to a complex dilation
-- statement:
--   Let $F$ be a real normed space, $\chi : \mathbb{C} \to \mathbb{C}$ and $\kappa \ne 0$, and suppose that $\chi(z)/z - \kappa$ decays like $e^{-bs}$ in $C^\infty$ ($b > 0$) in the cylindrical coordinates $z = e^{2\pi(s+it)}$ at $\infty$. If $f : \mathbb{C} \to F$ is such that $f(e^{2\pi(s+it)})$ decays like $e^{-b's}$ in $C^\infty$ ($b' \in \mathbb{R}$), then $f(\chi(e^{2\pi(s+it)}))$ decays like $e^{-b's}$ in $C^\infty$.
--
--   Role: the decay rate of a function at the puncture $\infty$ is unchanged by reparametrizing by a map asymptotic to a complex dilation, as needed to compare two graphs over different parametrizations of the plane.
--
--   Formalization Note: $e^{2\pi(s+it)}$ is `cylInf s t`; decay is `ExpDecayCInfty`.
-- source:
--   Standard calculus of exponential decay on cylindrical ends; used toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 6

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open Metric
open scoped ContDiff Real

/-- Decay is preserved by composition with a map asymptotic to `z ↦ κ z`. If `χ(z)/z - κ`
decays like `e^{-bs}` in `C^∞` in the cylindrical coordinates `z = e^{2π(s+it)}` (`κ ≠ 0`,
`b > 0`) and `f(z)` decays like `e^{-b's}` in `C^∞`, then so does `f(χ(z))`. -/
theorem expDecayCInfty_comp_of_div_sub {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (χ : ℂ → ℂ) (κ : ℂ) (hκ : κ ≠ 0) (b : ℝ) (hb : 0 < b)
    (has : ExpDecayCInfty (fun p : ℝ × ℝ => χ (cylInf p.1 p.2) / cylInf p.1 p.2 - κ) b)
    (f : ℂ → F) (b' : ℝ) (hf : ExpDecayCInfty (fun p : ℝ × ℝ => f (cylInf p.1 p.2)) b') :
    ExpDecayCInfty (fun p : ℝ × ℝ => f (χ (cylInf p.1 p.2))) b' := by
  sorry

end FiniteEnergyPlane
