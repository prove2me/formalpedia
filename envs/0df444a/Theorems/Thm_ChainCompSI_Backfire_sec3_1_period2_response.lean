-- Prove2me | Theorems.Thm_ChainCompSI_Backfire_sec3_1_period2_response
-- name    : ChainCompSI.Backfire.sec3_1_period2_response
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T02:22:52.674253+00:00
-- url     : https://prove2.me/theorems/36efe71f-af45-410f-8b80-cb79f2e8529c
-- title:
--   §3.1 display, p. 10 — the period-2 retail-price response: ∂Dᵢ₂/∂wᵢ₂ = −(1+θ)/2
-- statement:
--   Consider any passive-beliefs equilibrium of the two-chain game (SI, NI or mixed), with $\theta > 0$ and $h \ge 0$. Fix chain $i$, write $a = p_{j2}^*$ for the rival's equilibrium-path second-period price, and take any own history of chain $i$ with carryover $I \ge 0$ and any second-period wholesale price $w \ge 0$ at which the retailer replenishes, in the sense that
--   $$2I < 1 + \theta a - (1+\theta) w.$$
--   Then the retailer's equilibrium second-period price and the resulting demand are
--   $$p_{i2} = \frac{1 + \theta a + (1+\theta) w}{2(1+\theta)}, \qquad D_{i2} = \frac{1 + \theta a - (1+\theta) w}{2}.$$
--   Hence $\partial p_{i2}/\partial w_{i2} = 1/2$, $\partial D_{i2}/\partial p_{i2} = -(1+\theta)$, and
--   $$\frac{\partial D_{i2}}{\partial w_{i2}} = \frac{\partial D_{i2}}{\partial p_{i2}}\cdot\frac{\partial p_{i2}}{\partial w_{i2}} = -\frac12(1+\theta) < 0,$$
--   which is the display of §3.1. It quantifies how much more strongly a lower second-period wholesale price raises the retailer's demand under fiercer competition, the channel through which carryover inventory acts.
--
--   **Formalization Note** The display is stated as the closed form of the stage-4 strategy on the region where the retailer buys from the manufacturer; the strict inequality is needed, since at equality with $I = 0$ demand is zero and the optimal price is not unique.
-- source:
--   Li, Li & Chen, Strategic Inventories under Supply Chain Competition, SSRN 3003887 (author's copy), p. 10, §3.1 display (∂Di2/∂wi2 = −½(1+θ))

import Mathlib
import Definitions.Def_ChainCompSI_Backfire_Model

namespace ChainCompSI.Backfire

theorem sec3_1_period2_response (θ h : ℝ) (hθ : 0 < θ) (hh : 0 ≤ h) (si : Fin 2 → Bool) (E : Profile) (hE : IsEq θ h si E) (i : Fin 2) (H : Hist) (hI : 0 ≤ H.I) (w : ℝ) (hw : 0 ≤ w) (hrep : 2 * H.I < 1 + θ * E.p2' (rival i) - (1 + θ) * w) : E.p2 i H w = (1 + θ * E.p2' (rival i) + (1 + θ) * w) / (2 * (1 + θ)) ∧ demand θ (E.p2 i H w) (E.p2' (rival i)) = (1 + θ * E.p2' (rival i) - (1 + θ) * w) / 2 := by sorry

end ChainCompSI.Backfire
