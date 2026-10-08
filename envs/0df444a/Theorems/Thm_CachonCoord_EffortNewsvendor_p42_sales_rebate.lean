-- Prove2me | Theorems.Thm_CachonCoord_EffortNewsvendor_p42_sales_rebate
-- name    : CachonCoord.EffortNewsvendor.p42_sales_rebate
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:32:43.625509+00:00
-- url     : https://prove2.me/theorems/f77db64b-09ae-4466-8d8a-4cd43372e085
-- title:
--   §6.4.1, pp. 42–43 — with a sales rebate r > 0 and q > t the retailer over-rewards effort: ∂π_r/∂e > ∂Π/∂e
-- statement:
--   In the effort model of §6.4.1, consider a sales rebate contract with wholesale price $w_s$, rebate $r > 0$ and threshold $t \ge 0$. The retailer's profit is $\pi_r = pS(q, e) - T_s(q, w_s, r, t) - g(e)$, where for $q \ge t$ the transfer is $T_s = (w_s - r)q + r\big(t + \int_t^q F(y \mid e)\,dy\big)$. For every $q > t$ and $e > 0$ both $\pi_r$ and $\Pi$ are differentiable in $e$, and
--
--   $$
--   \frac{\partial \pi_r(q, e, w_s, r, t)}{\partial e} > \frac{\partial \Pi(q, e)}{\partial e}.
--   $$
--
--   The retailer therefore exerts too much effort.
--
--   **Formalization Note** The transfer and profit are §6.2.6's (p. 27) with $v = g_r = c_r = 0$, $F$ replaced by $F(\cdot \mid e)$, and the effort cost subtracted. The threshold $t \ge 0$ (a number of units; the page takes $t \in [0, q^o]$ on p. 27) is a disclosed addition. With $t < q \le 0$ the integral term would not depend on effort.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.4.1, pp. 42–43, the display after "for r > 0 and q > t"; transfer from §6.2.6, p. 27

import Mathlib
import Definitions.Def_CachonCoord_EffortNewsvendor_Model
import Definitions.Def_CachonCoord_EffortNewsvendor_Contracts

namespace CachonCoord.EffortNewsvendor

/-- pp. 42–43, the display after "for r > 0 and q > t": with a sales rebate contract
`{w_s, r, t}`, `r > 0` and threshold `t ≥ 0`, at every `q > t` and `e > 0`,
`∂π_r(q, e, w_s, r, t)/∂e > ∂Π(q, e)/∂e` (both derivatives exist). -/
theorem p42_sales_rebate (M : Model) (ws r t q e : ℝ) (hr : 0 < r) (ht : 0 ≤ t) (hqt : t < q)
    (he : 0 < e) :
    ∃ d₁ d₂ : ℝ, HasDerivAt (fun e' => M.srRetailerProfit ws r t q e') d₁ e ∧
      HasDerivAt (fun e' => M.Pi q e') d₂ e ∧ d₂ < d₁ := by sorry

end CachonCoord.EffortNewsvendor
