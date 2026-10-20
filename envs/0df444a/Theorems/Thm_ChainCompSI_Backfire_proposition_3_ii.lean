-- Prove2me | Theorems.Thm_ChainCompSI_Backfire_proposition_3_ii
-- name    : ChainCompSI.Backfire.proposition_3_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:22:53.334012+00:00
-- url     : https://prove2.me/theorems/74b2b134-0e08-4c7f-a3c8-68d6719bbcd7
-- title:
--   Proposition 3(ii), p. 15 — retailers' equilibrium profit strictly increases in h near 1/(4+θ)
-- statement:
--   Let $\theta > 0$, and let $0 \le h < h'$ be two holding costs with
--   $$\frac{1888 + 1424\theta + 242\theta^2 - 35\theta^3}{9728 + 11456\theta + 5344\theta^2 + 1148\theta^3 + 98\theta^4} \le h < h' \le \frac{1}{4+\theta}.$$
--   Then the strategic-inventory games with holding costs $h$ and $h'$ both have passive-beliefs equilibria, and for any equilibrium $E$ at $h$ and any equilibrium $E'$ at $h'$, each retailer earns strictly more at the higher cost:
--   $$\pi_i(E) < \pi_i(E').$$
--   Here $\pi_i$ is the retailer's realized profit including the holding cost $h I_i$, so $h$ enters both through the equilibrium and through the cost term. Together with part (i), this shows that near the threshold $1/(4+\theta)$ every firm benefits from a costlier carryover.
--
--   **Formalization Note** $h \ge 0$ is the standing assumption on the holding cost.
-- source:
--   Li, Li & Chen, Strategic Inventories under Supply Chain Competition, SSRN 3003887 (author's copy), p. 15, Proposition 3(ii)

import Mathlib
import Definitions.Def_ChainCompSI_Backfire_Model

namespace ChainCompSI.Backfire

theorem proposition_3_ii (θ h h' : ℝ) (hθ : 0 < θ) (hh : 0 ≤ h) (hlo : (1888 + 1424 * θ + 242 * θ ^ 2 - 35 * θ ^ 3) / (9728 + 11456 * θ + 5344 * θ ^ 2 + 1148 * θ ^ 3 + 98 * θ ^ 4) ≤ h) (hlt : h < h') (hhi : h' ≤ 1 / (4 + θ)) : (∃ E, IsEq θ h SI E) ∧ (∃ E', IsEq θ h' SI E') ∧ ∀ E E', IsEq θ h SI E → IsEq θ h' SI E' → ∀ i : Fin 2, retProfit θ h E i < retProfit θ h' E' i := by sorry

end ChainCompSI.Backfire
