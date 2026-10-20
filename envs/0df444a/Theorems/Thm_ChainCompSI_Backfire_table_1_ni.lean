-- Prove2me | Theorems.Thm_ChainCompSI_Backfire_table_1_ni
-- name    : ChainCompSI.Backfire.table_1_ni
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:23:00.929621+00:00
-- url     : https://prove2.me/theorems/03424568-fc39-4e08-bc3c-1b4805458880
-- title:
--   Table 1, right column, p. 9 — the NI equilibrium (also SI when h > 1/(4+θ))
-- statement:
--   Let $\theta > 0$ and $h \ge 0$. Consider either the no-inventory game (NI), or the strategic-inventory game (SI) with $h > 1/(4+\theta)$, i.e. $h(4+\theta) > 1$. Then a passive-beliefs equilibrium exists, and in **every** equilibrium each chain $i \in \{1,2\}$ has
--   $$w_{i1} = w_{i2} = \frac{2}{4+\theta}, \quad p_{i1} = p_{i2} = \frac{3}{4+\theta}, \quad D_{i1} = D_{i2} = \frac{1+\theta}{4+\theta}, \quad I_i = 0,$$
--   and the equilibrium profits are
--   $$\Pi_i = \frac{4(1+\theta)}{(4+\theta)^2}, \qquad \pi_i = \frac{2(1+\theta)}{(4+\theta)^2}.$$
--   This is the benchmark against which the paper measures the effect of strategic inventory; it also shows that a high holding cost removes strategic inventory altogether.
--
--   **Formalization Note** The demands are realized demands at both chains' equilibrium-path prices, and the profits are realized profits. The claim covers every equilibrium profile, asymmetric ones included.
-- source:
--   Li, Li & Chen, Strategic Inventories under Supply Chain Competition, SSRN 3003887 (author's copy), p. 9, Table 1, right column (SI with h > 1/(4+θ), or NI)

import Mathlib
import Definitions.Def_ChainCompSI_Backfire_Model

namespace ChainCompSI.Backfire

theorem table_1_ni (θ h : ℝ) (hθ : 0 < θ) (hh : 0 ≤ h) (si : Fin 2 → Bool) (hsi : si = NI ∨ (si = SI ∧ 1 < h * (4 + θ))) : (∃ E, IsEq θ h si E) ∧ ∀ E, IsEq θ h si E → ∀ i : Fin 2, E.w1 i = 2 / (4 + θ) ∧ E.p1 i = 3 / (4 + θ) ∧ E.D1 θ i = (1 + θ) / (4 + θ) ∧ E.inv i = 0 ∧ E.w2' i = 2 / (4 + θ) ∧ E.p2' i = 3 / (4 + θ) ∧ E.D2 θ i = (1 + θ) / (4 + θ) ∧ mfrProfit θ E i = 4 * (1 + θ) / (4 + θ) ^ 2 ∧ retProfit θ h E i = 2 * (1 + θ) / (4 + θ) ^ 2 := by sorry

end ChainCompSI.Backfire
