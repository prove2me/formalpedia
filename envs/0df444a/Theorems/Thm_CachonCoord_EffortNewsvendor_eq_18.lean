-- Prove2me | Theorems.Thm_CachonCoord_EffortNewsvendor_eq_18
-- name    : CachonCoord.EffortNewsvendor.eq_18
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:18:43.064298+00:00
-- url     : https://prove2.me/theorems/1c01f825-24d9-415e-a61d-ff02bcab3ae0
-- title:
--   Eq. (18), p. 42 — the optimal effort e°(q) satisfies p ∂S(q, e°(q))/∂e − g′(e°(q)) = 0
-- statement:
--   In the effort model of §6.4.1, fix an order quantity $q \ge 0$ and suppose an effort level $e^o(q) > 0$ maximizes the channel profit $e \mapsto \Pi(q, e) = pS(q, e) - cq - g(e)$ over $e \ge 0$. Then $\Pi(q, \cdot)$ is differentiable at $e^o(q)$ and
--
--   $$
--   \frac{\partial \Pi(q, e^o(q))}{\partial e} = p\,\frac{\partial S(q, e^o(q))}{\partial e} - g'(e^o(q)) = 0,
--   \qquad \frac{\partial S(q, e)}{\partial e} = -\int_0^q \frac{\partial F(y \mid e)}{\partial e}\,dy.
--   $$
--
--   This first-order condition characterizes the chain-optimal effort for a given order quantity. The contract results of the section compare the retailer's effort incentive with it.
--
--   **Formalization Note** The maximizer is assumed interior ($e^o(q) > 0$), where the book's first-order condition applies.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.4.1, Eq. (18), p. 42

import Mathlib
import Definitions.Def_CachonCoord_EffortNewsvendor_Model

namespace CachonCoord.EffortNewsvendor

/-- Eq. (18), p. 42: if `e°(q) > 0` maximizes the channel profit `e ↦ Π(q, e)` over effort
levels `e ≥ 0`, then `Π(q, ·)` is differentiable at `e°(q)` with derivative
`p ∂S(q, e°(q))/∂e − g′(e°(q))`, where `∂S(q, e)/∂e = −∫_0^q ∂F(y|e)/∂e dy`, and this derivative
is `0`. -/
theorem eq_18 (M : Model) (q eo : ℝ) (hq : 0 ≤ q) (heo : 0 < eo)
    (hmax : IsMaxOn (fun e => M.Pi q e) (Set.Ici 0) eo) :
    HasDerivAt (fun e => M.Pi q e)
        (M.p * (-∫ y in (0 : ℝ)..q, M.effortSlope y eo) - M.effortCost' eo) eo ∧
      M.p * (-∫ y in (0 : ℝ)..q, M.effortSlope y eo) - M.effortCost' eo = 0 := by sorry

end CachonCoord.EffortNewsvendor
