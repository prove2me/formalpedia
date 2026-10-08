-- Prove2me | Theorems.Thm_CachonCoord_EffortNewsvendor_p42_quantity_flexibility
-- name    : CachonCoord.EffortNewsvendor.p42_quantity_flexibility
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:32:47.989078+00:00
-- url     : https://prove2.me/theorems/10ebe77e-2282-4850-906c-02c140df6840
-- title:
--   §6.4.1, p. 42 — with quantity flexibility δ > 0 the retailer under-rewards effort: ∂π_r/∂e < ∂Π/∂e
-- statement:
--   In the effort model of §6.4.1, consider a quantity-flexibility contract with wholesale price $w_q > 0$ and flexibility $\delta \in (0, 1]$. The retailer's profit is
--
--   $$
--   \pi_r(q, e, w_q, \delta) = pS(q, e) - w_q\Big(q - \int_{(1-\delta)q}^q F(y \mid e)\,dy\Big) - g(e).
--   $$
--
--   For every $q > 0$ and $e > 0$ both $\pi_r$ and $\Pi$ are differentiable in $e$, and
--
--   $$
--   \frac{\partial \pi_r(q, e, w_q, \delta)}{\partial e} < \frac{\partial \Pi(q, e)}{\partial e}.
--   $$
--
--   The retailer therefore chooses less than the optimal effort, and the quantity-flexibility contract does not coordinate in this setting.
--
--   **Formalization Note** The range $\delta \le 1$ is the contract's range in §6.2.5 (p. 24). The hypotheses $w_q > 0$ and $q > 0$ are added: the page leaves them implicit, and with $w_q = 0$ or $q = 0$ the two derivatives coincide.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.4.1, p. 42, the display after "For all δ > 0"; contract range δ ∈ [0, 1] from §6.2.5, p. 24

import Mathlib
import Definitions.Def_CachonCoord_EffortNewsvendor_Model
import Definitions.Def_CachonCoord_EffortNewsvendor_Contracts

namespace CachonCoord.EffortNewsvendor

/-- p. 42, the display after "For all δ > 0": with a quantity-flexibility contract `{w_q, δ}`,
`0 < δ ≤ 1` and wholesale price `w_q > 0`, at every `q > 0` and `e > 0`,
`∂π_r(q, e, w_q, δ)/∂e < ∂Π(q, e)/∂e` (both derivatives exist). -/
theorem p42_quantity_flexibility (M : Model) (wq δ q e : ℝ) (hwq : 0 < wq) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hq : 0 < q) (he : 0 < e) :
    ∃ d₁ d₂ : ℝ, HasDerivAt (fun e' => M.qfRetailerProfit wq δ q e') d₁ e ∧
      HasDerivAt (fun e' => M.Pi q e') d₂ e ∧ d₁ < d₂ := by sorry

end CachonCoord.EffortNewsvendor
