-- Prove2me | Theorems.Thm_CachonCoord_CapacityForecast_p98_expected_sales
-- name    : CachonCoord.CapacityForecast.p98_expected_sales
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:57:08.255353+00:00
-- url     : https://prove2.me/theorems/5e5c0c26-5604-42c4-8fb8-4dea6787250c
-- title:
--   §6.10.2, p. 98 — expected sales S_θ(x) = x − E[(x − D_θ)⁺] = x − ∫₀ˣ F_θ
-- statement:
--   Let $D_\theta$ be demand of type $\theta$ in the capacity procurement game, with distribution function $F_\theta$ vanishing on $(-\infty, 0)$. For every $x$, expected sales with $x$ units of capacity satisfy
--   $$S_\theta(x) = x - \mathbb E\big[(x - D_\theta)^+\big] = x - \int_0^x F_\theta(y)\,dy .$$
--
--   The integral form is the one used to differentiate $S_\theta$ and the chain profit $\Omega_\theta$ in capacity.
--
--   **Formalization Note** The identity is stated for every real $x$ (for $x < 0$ both sides equal $x$). The page writes the integration variable as $x$.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.10.2, p. 98, the display defining S_θ(x)

import Mathlib
import Definitions.Def_CachonCoord_CapacityForecast_Model

open MeasureTheory ProbabilityTheory

namespace CachonCoord.CapacityForecast

/-- Cachon (2003), 3rd draft, §6.10.2, p. 98, the display defining `S_θ(x)`: expected sales
`S_θ(x) = x − E[(x − D_θ)⁺]` equal `x − ∫_0^x F_θ(y) dy`. (The page writes the integration
variable as `x`.) -/
theorem p98_expected_sales (M : Model) (θ : DemandType) (x : ℝ) :
    M.S θ x = x - ∫ y in (0 : ℝ)..x, cdf (M.μ θ) y := by sorry

end CachonCoord.CapacityForecast
