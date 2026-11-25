-- Prove2me | Theorems.Thm_Arxiv2608_05214_traveltime_webster_horn
-- name    : Arxiv2608_05214.traveltime_webster_horn
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T19:14:59.367795+00:00
-- url     : https://prove2.me/theorems/f53844e5-90ae-4488-8900-20db5a6e61b6
-- title:
--   Eq. (15): the traveltime coordinate turns the 1D wave equation into Webster's horn equation
-- statement:
--   Let $c:\mathbb R\to(0,\infty)$ be continuous, let $\tau(x)=\int_0^x dx'/c(x')$ be the one-way traveltime, and let $\rho:\mathbb R\to\mathbb R$ be a density. Let $Z:\mathbb R\to\mathbb R$ be the impedance as a function of traveltime, $\rho(x)c(x)=Z(\tau(x))$ for all $x$. Let $w(\tau,t)$ be a field that is differentiable in $\tau$ and for which $\tau\mapsto Z(\tau)\,\partial_\tau w(\tau,t)$ is differentiable, and let $u(x,t)=w(\tau(x),t)$ be the same field in depth. Then for all $x,t$
--
--   $$c(x)\Big[\rho\,\partial_t^2u-\partial_x\big(\rho c^2\,\partial_xu\big)\Big](x,t)=\Big[Z\,\partial_t^2w-\partial_\tau\big(Z\,\partial_\tau w\big)\Big](\tau(x),t).$$
--
--   In particular $u$ satisfies the 1D wave equation (14) at $(x,t)$ if and only if $w$ satisfies Webster's horn equation (15) at $(\tau(x),t)$. In traveltime the medium enters only through the impedance $\rho c$.
--
--   **Formalization Note** The field is taken in traveltime form, $u=w\circ\tau$, so that the chain rule applies to the differentiable function $w$. The paper's further remarks that only $\rho c$ can be recovered from surface data, and that separating $\rho$ and $c$ needs particle-velocity data, are asserted without proof and are not part of the statement.
-- source:
--   H. A. Oyekan, Marchenko Theory, Algorithms, and Applications: A Review, arXiv:2608.05214v1 (2026), claim c001; Section III-B (Step 1), eqs. (14)-(15), PDF p. 4

import Mathlib
import Definitions.Def_Arxiv2608_05214_Basic

open MeasureTheory Filter Topology
open scoped ContDiff

namespace Arxiv2608_05214

theorem traveltime_webster_horn (ρ c Z : ℝ → ℝ) (w : ℝ → ℝ → ℝ)
    (hc : Continuous c) (hcpos : ∀ x, 0 < c x)
    (hZ : ∀ x, ρ x * c x = Z (travelTime c x))
    (hw : ∀ τ t, DifferentiableAt ℝ (fun τ => w τ t) τ)
    (hflux : ∀ τ t, DifferentiableAt ℝ (fun τ => Z τ * deriv (fun τ => w τ t) τ) τ) :
    ∀ x t : ℝ,
      c x * waveEqLHS ρ c (fun x t => w (travelTime c x) t) x t = hornEqLHS Z w (travelTime c x) t ∧
      (waveEqLHS ρ c (fun x t => w (travelTime c x) t) x t = 0 ↔
        hornEqLHS Z w (travelTime c x) t = 0) := by sorry

end Arxiv2608_05214
