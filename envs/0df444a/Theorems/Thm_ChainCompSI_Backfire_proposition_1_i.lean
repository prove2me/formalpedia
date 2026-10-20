-- Prove2me | Theorems.Thm_ChainCompSI_Backfire_proposition_1_i
-- name    : ChainCompSI.Backfire.proposition_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:22:56.489662+00:00
-- url     : https://prove2.me/theorems/63d4965b-e756-4269-9836-0d5ff669c0f7
-- title:
--   Proposition 1(i), p. 9 — strategic inventory exists in equilibrium iff h < 1/(4+θ)
-- statement:
--   Let $\theta > 0$ and $h \ge 0$. The strategic-inventory game has a passive-beliefs equilibrium, and in every equilibrium each chain $i$ carries a strictly positive inventory if and only if the holding cost is small:
--   $$I_i > 0 \iff h < \frac{1}{4+\theta}.$$
--   So supply-chain competition does not eliminate strategic inventory, but it is held only when holding it is cheap enough, with a threshold that falls as competition intensifies.
-- source:
--   Li, Li & Chen, Strategic Inventories under Supply Chain Competition, SSRN 3003887 (author's copy), p. 9, Proposition 1(i)

import Mathlib
import Definitions.Def_ChainCompSI_Backfire_Model

namespace ChainCompSI.Backfire

theorem proposition_1_i (θ h : ℝ) (hθ : 0 < θ) (hh : 0 ≤ h) : (∃ E, IsEq θ h SI E) ∧ ∀ E, IsEq θ h SI E → ∀ i : Fin 2, (0 < E.inv i ↔ h < 1 / (4 + θ)) := by sorry

end ChainCompSI.Backfire
