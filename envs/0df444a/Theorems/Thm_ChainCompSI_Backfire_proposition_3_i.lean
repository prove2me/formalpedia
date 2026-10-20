-- Prove2me | Theorems.Thm_ChainCompSI_Backfire_proposition_3_i
-- name    : ChainCompSI.Backfire.proposition_3_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:22:54.707204+00:00
-- url     : https://prove2.me/theorems/91527262-cac7-4c17-aa9d-62fe708f82a2
-- title:
--   Proposition 3(i), p. 15 — manufacturers' equilibrium profit strictly increases in h on [17(4−θ)/(272+136θ+21θ²), 1/(4+θ)]
-- statement:
--   Let $\theta > 0$, and let $0 \le h < h'$ be two holding costs with
--   $$\frac{17(4-\theta)}{272 + 136\theta + 21\theta^2} \le h < h' \le \frac{1}{4+\theta}.$$
--   Then the strategic-inventory games with holding costs $h$ and $h'$ both have passive-beliefs equilibria, and for any equilibrium $E$ at $h$ and any equilibrium $E'$ at $h'$, each manufacturer earns strictly more at the higher cost:
--   $$\Pi_i(E) < \Pi_i(E').$$
--   In contrast to the monopoly chain of Anand et al. (2008), where a higher holding cost always hurts the manufacturer, under competition it can help, because it reduces strategic inventory and softens competition between the chains.
--
--   **Formalization Note** $h \ge 0$ is the standing assumption on the holding cost; for $\theta \ge 4$ the printed lower bound is $\le 0$, and the interval is $[0, 1/(4+\theta)]$.
-- source:
--   Li, Li & Chen, Strategic Inventories under Supply Chain Competition, SSRN 3003887 (author's copy), p. 15, Proposition 3(i)

import Mathlib
import Definitions.Def_ChainCompSI_Backfire_Model

namespace ChainCompSI.Backfire

theorem proposition_3_i (θ h h' : ℝ) (hθ : 0 < θ) (hh : 0 ≤ h) (hlo : 17 * (4 - θ) / (272 + 136 * θ + 21 * θ ^ 2) ≤ h) (hlt : h < h') (hhi : h' ≤ 1 / (4 + θ)) : (∃ E, IsEq θ h SI E) ∧ (∃ E', IsEq θ h' SI E') ∧ ∀ E E', IsEq θ h SI E → IsEq θ h' SI E' → ∀ i : Fin 2, mfrProfit θ E i < mfrProfit θ E' i := by sorry

end ChainCompSI.Backfire
