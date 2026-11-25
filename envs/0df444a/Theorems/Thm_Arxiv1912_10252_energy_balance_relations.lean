-- Prove2me | Theorems.Thm_Arxiv1912_10252_energy_balance_relations
-- name    : Arxiv1912_10252.energy_balance_relations
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T07:08:31.041498+00:00
-- url     : https://prove2.me/theorems/b6f08932-dcc4-5084-ad0e-ef30a96efb16
-- title:
--   Eqs. (18), (20), (21) (as proved): energy-balance relations of the two-port model
-- statement:
--   Let $\kappa_c>0$, $\sigma>0$, $L>0$ and $Q_0\ne0$, let $H\in\mathbb R$, and let the channel slopes $C_1(x_a),D_1(x_a),C_2(x_a),C_1(x_b),D_2(x_b),C_2(x_b)$ satisfy the energy balance (16). Let $\mathbf G$ and $\mathbf Q$ be the matrices of Eqs. (17) and (19), with $\mathbf G$ at leading order in $L$. Then
--
--   $$\mathbf G_{11}+\mathbf G_{21}=\mathbf G_{12}+\mathbf G_{22},\qquad \mathbf Q_{12}=\frac{\kappa_c\mathbf G_{12}}{L},\qquad \mathbf Q_{21}=-\frac{\kappa_c\mathbf G_{21}}{L},\qquad \mathbf Q_{11}+\mathbf Q_{22}=\mathbf Q_{12}+\mathbf Q_{21}.$$
--
--   These are the relations that the paper's proof of the equivalence between steady-state global reciprocity and the absence of the diode effect draws from energy conservation.
--
--   **Formalization Note** The paper prints Eq. (18) as $\mathbf G_{11}+\mathbf G_{12}=\mathbf G_{22}+\mathbf G_{21}$ and Eq. (20) as $\mathbf Q_{12}=\kappa_c\mathbf G_{21}/L$, $\mathbf Q_{21}=-\kappa_c\mathbf G_{12}/L$. Its own Eqs. (15)-(17) and (19) give the relations above, which are the printed ones with $\mathbf G_{12}$ and $\mathbf G_{21}$ exchanged. The printed versions hold only when $\mathbf G_{12}=\mathbf G_{21}$. Eq. (21) is as printed. The hypothesis $Q_0\ne0$ is the standing assumption of the section and is not needed for these identities.
-- source:
--   Li, Li, Qi, Qiu and Chen, Diffusive non-reciprocity and thermal diode, arXiv:1912.10252v3 (2019), claim c020; Section IV, Eqs. (15)-(21), PDF p. 6

import Mathlib
import Definitions.Def_Arxiv1912_10252_Basic

open Matrix

namespace Arxiv1912_10252

theorem energy_balance_relations (s : TwoPortData) (hkc : 0 < s.kc) (hsigma : 0 < s.sigma)
    (hL : 0 < s.L) (hQ0 : s.Q0 ≠ 0) (hE : EnergyConservation s) :
    greenMat s 0 0 + greenMat s 1 0 = greenMat s 0 1 + greenMat s 1 1 ∧
    fluxMat s 0 1 = s.kc * greenMat s 0 1 / s.L ∧
    fluxMat s 1 0 = -(s.kc * greenMat s 1 0 / s.L) ∧
    fluxMat s 0 0 + fluxMat s 1 1 = fluxMat s 0 1 + fluxMat s 1 0 := by sorry

end Arxiv1912_10252
