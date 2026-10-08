-- Prove2me | Theorems.Thm_CachonCoord_InternalMarket_p94_manager_effort
-- name    : CachonCoord.InternalMarket.p94_manager_effort
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:09:58.904245+00:00
-- url     : https://prove2.me/theorems/5c0963c1-3aea-45a1-b43a-c15f0a0f222e
-- title:
--   §6.9.1, p. 94 — paid (46) per unit of output, the manager's unique optimal effort is e°, and the supplier's expected market profit is zero
-- statement:
--   In the model of §6.9.1, assume the integrand of $K=E\big[(A_1^\eta+A_2^\eta)^{1/\eta}Y^{(\eta-1)/\eta}\big]$ is integrable, $E[Y]>0$, and $e^o>0$ satisfies (45):
--   $$
--   \Big(\frac{\eta-1}{\eta}\Big)(e^o)^{-1/\eta}K-c'(e^o)=0.
--   $$
--   Let the supplier pay the production manager the amount (46) per unit of realized output, so that his expected utility from effort $e\ge0$ is $u(e)=(\text{payment per unit})\cdot E[Ye]-c(e)$. Then:
--
--   1. for every $e>0$,
--   $$
--   u'(e)=\Big(\frac{\eta-1}{\eta}\Big)(e^o)^{-1/\eta}K-c'(e);
--   $$
--   2. $e^o$ is the manager's unique optimal effort over $[0,\infty)$;
--   3. the supplier's expected profit from the internal market is zero: $E[Q\,w(A,Q)\mid e^o]-(\text{payment per unit})\cdot E[Q\mid e^o]=0$.
--
--   So the internal market together with the payment (46) induces the supply chain optimal effort, with the supplier breaking even.
--
--   **Formalization Note** $E[Y]>0$ is added as in (46). The page states $u(e)=((\eta-1)/\eta)(e^o)^{-1/\eta}Ke-c(e)$ directly; here $u$ is defined from the payment scheme (payment rate times expected output, minus cost), and the printed form is a consequence.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.9.1, p. 94, u(e), u′(e) and the two following sentences

import Mathlib
import Definitions.Def_CachonCoord_InternalMarket_Revenue
import Definitions.Def_CachonCoord_InternalMarket_Model

namespace CachonCoord.InternalMarket

open MeasureTheory

/-- §6.9.1, p. 94 (Cachon 2003, 3rd draft). Assume `K = E[(A₁^η + A₂^η)^{1/η} Y^{(η−1)/η}]` is
integrable, `E[Y] > 0`, and `e° > 0` satisfies (45):
`((η − 1)/η)(e°)^{−1/η} K − c'(e°) = 0`. Let the supplier pay the production manager the rate (46)
per unit of realized output, so that his expected utility is `u(e) = payRate(e°) · E[Ye] − c(e)`. Then
1. `u'(e) = ((η − 1)/η)(e°)^{−1/η} K − c'(e)` for every `e > 0`;
2. `e°` is the manager's unique optimal effort over `[0, ∞)`;
3. the supplier earns zero expected profit from the internal market at `e°`:
   `E[Q w(A, Q) | e°] − payRate(e°) · E[Q | e°] = 0`. -/
theorem p94_manager_effort {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (hint : Integrable (fun ω => (M.A₁ ω ^ M.η + M.A₂ ω ^ M.η) ^ (1 / M.η) *
      M.Y ω ^ ((M.η - 1) / M.η)) M.P)
    (hY : 0 < ∫ ω, M.Y ω ∂M.P) (eo : ℝ) (heo : 0 < eo)
    (h45 : (M.η - 1) / M.η * eo ^ (-1 / M.η) * M.K - M.c' eo = 0) :
    (∀ e : ℝ, 0 < e → HasDerivAt (M.managerUtility eo)
      ((M.η - 1) / M.η * eo ^ (-1 / M.η) * M.K - M.c' e) e) ∧
    IsMaxOn (M.managerUtility eo) (Set.Ici 0) eo ∧
    (∀ e : ℝ, 0 ≤ e → IsMaxOn (M.managerUtility eo) (Set.Ici 0) e → e = eo) ∧
    M.expMarketRevenue eo - M.payRate eo * M.expOutput eo = 0 := by sorry

end CachonCoord.InternalMarket
