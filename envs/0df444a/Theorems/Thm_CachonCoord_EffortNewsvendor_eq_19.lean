-- Prove2me | Theorems.Thm_CachonCoord_EffortNewsvendor_eq_19
-- name    : CachonCoord.EffortNewsvendor.eq_19
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:31:52.848217+00:00
-- url     : https://prove2.me/theorems/176ecccb-47ab-4666-8c8d-607003561c7d
-- title:
--   Eq. (19), p. 42 — with a buy back b > 0 the retailer under-rewards effort: ∂π_r/∂e < ∂Π/∂e
-- statement:
--   In the effort model of §6.4.1, consider a buy back contract with wholesale price $w_b$ and buy back price $b > 0$. The retailer's profit is $\pi_r(q, e, w_b, b) = (p - b)S(q, e) - (w_b - b)q - g(e)$. For every order quantity $q > 0$ and effort level $e > 0$, both $\pi_r$ and $\Pi$ are differentiable in $e$, and
--
--   $$
--   \frac{\partial \pi_r(q, e, w_b, b)}{\partial e} < \frac{\partial \Pi(q, e)}{\partial e}.
--   $$
--
--   So $e^o$ cannot be the retailer's optimal effort when $b > 0$. Since $b > 0$ is required to coordinate the order quantity, the buy back contract cannot coordinate this supply chain.
--
--   **Formalization Note** The book's inequality is stated for an order quantity $q > 0$ and an interior effort $e > 0$. At $q = 0$ both derivatives equal $-g'(e)$.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.4.1, Eq. (19), p. 42

import Mathlib
import Definitions.Def_CachonCoord_EffortNewsvendor_Model
import Definitions.Def_CachonCoord_EffortNewsvendor_Contracts

namespace CachonCoord.EffortNewsvendor

/-- Eq. (19), p. 42: with a buy back contract `{w_b, b}` and `b > 0`, at every order
quantity `q > 0` and effort `e > 0` the retailer's marginal profit of effort is strictly below
the channel's: `∂π_r(q, e, w_b, b)/∂e < ∂Π(q, e)/∂e` (both derivatives exist). -/
theorem eq_19 (M : Model) (wb b q e : ℝ) (hb : 0 < b) (hq : 0 < q) (he : 0 < e) :
    ∃ d₁ d₂ : ℝ, HasDerivAt (fun e' => M.bbRetailerProfit wb b q e') d₁ e ∧
      HasDerivAt (fun e' => M.Pi q e') d₂ e ∧ d₁ < d₂ := by sorry

end CachonCoord.EffortNewsvendor
