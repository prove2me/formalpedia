-- Prove2me | Theorems.Thm_FZEchelon_NormalDemand_Theta_deriv
-- name    : FZEchelon.NormalDemand.Theta_deriv
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T11:23:57.071427+00:00
-- url     : https://prove2.me/theorems/c573da05-8004-4952-9709-fbcf12b57eae
-- title:
--   §4, p. 830 — $\Theta'(x)=\Phi(x)$
-- statement:
--   Let $\Phi$ and $\phi$ be the standard normal cdf and density, and $\Theta(x)=x\Phi(x)+\phi(x)$. Then for every real $x$,
--   $$\Theta'(x)=\Phi(x).$$
--
--   This is the parenthetical note on p. 830, used when differentiating $\iota$ and $\kappa$.
-- source:
--   Federgruen and Zipkin, Computational Issues in an Infinite-Horizon, Multiechelon Inventory Model, Oper. Res. 32(4), 1984, p. 830, note after the definition of Θ

import Mathlib
import Definitions.Def_FZEchelon_NormalDemand_BivariateNormal

open MeasureTheory ProbabilityTheory Real

namespace FZEchelon.NormalDemand

theorem Theta_deriv : ∀ x : ℝ, HasDerivAt Theta (stdNormalCDF x) x := by sorry

end FZEchelon.NormalDemand
