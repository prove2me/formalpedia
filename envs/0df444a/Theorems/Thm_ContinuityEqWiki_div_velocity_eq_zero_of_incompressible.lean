-- Prove2me | Theorems.Thm_ContinuityEqWiki_div_velocity_eq_zero_of_incompressible
-- name    : ContinuityEqWiki.div_velocity_eq_zero_of_incompressible
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:29:11.024151+00:00
-- url     : https://prove2.me/theorems/ba7e93ce-8ea0-40b9-a30b-5727d59226d7
-- title:
--   Incompressible flow: mass continuity reduces to $\nabla\cdot\mathbf u=0$
-- statement:
--   Let $\rho:\mathbb R\times\mathbb R^3\to\mathbb R$ be a fluid density, $C^1$ jointly in $(t,x)$ and strictly positive, and let $\mathbf u:\mathbb R\times\mathbb R^3\to\mathbb R^3$ be a flow velocity field with $\mathbf u(t,\cdot)$ of class $C^1$ for every $t$. Suppose the mass continuity equation
--   $$\frac{\partial\rho}{\partial t}+\nabla\cdot(\rho\mathbf u)=0$$
--   holds everywhere, and that the flow is incompressible, i.e. the material derivative of the density vanishes:
--   $$\frac{\partial\rho}{\partial t}+\mathbf u\cdot\nabla\rho=0 .$$
--   Then the velocity field is divergence-free everywhere:
--   $$\nabla\cdot\mathbf u=0 .$$
--
--   This is the volume continuity equation of the source's *Fluid dynamics* section.
--
--   **Formalization Note** The source describes incompressibility parenthetically as "volumetric strain rate is zero". Taken literally that is already $\nabla\cdot\mathbf u=0$, so incompressibility is encoded here by the standard condition $D\rho/Dt=0$, which makes the reduction a real statement.
-- source:
--   Wikipedia, "Continuity equation", revision oldid=1378634825, https://en.wikipedia.org/w/index.php?title=Continuity_equation&oldid=1378634825, section "Fluid dynamics" (mass continuity equation and the volume continuity equation for incompressible fluids)

import Mathlib
import Definitions.Def_ContinuityEqWiki_Defs

namespace ContinuityEqWiki

theorem div_velocity_eq_zero_of_incompressible (ρ : ℝ → Space → ℝ) (u : ℝ → Space → Space)
    (hρ : ContDiff ℝ 1 (Function.uncurry ρ)) (hu : ∀ t, ContDiff ℝ 1 (u t))
    (hpos : ∀ t x, 0 < ρ t x)
    (mass : ∀ t x, timeDeriv ρ t x + div (fun y => ρ t y • u t y) x = 0)
    (incompressible : ∀ t x, timeDeriv ρ t x + ∑ i, u t x i * partialDeriv i (ρ t) x = 0) :
    ∀ t x, div (u t) x = 0 := by sorry

end ContinuityEqWiki
