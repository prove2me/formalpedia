-- Prove2me | Theorems.Thm_Arxiv1912_10252_reciprocal_implies_not_diode
-- name    : Arxiv1912_10252.reciprocal_implies_not_diode
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T07:19:07.740842+00:00
-- url     : https://prove2.me/theorems/b8905da1-ddc5-43b6-9394-b38463c37b8d
-- title:
--   Section IV: a steady-state globally reciprocal two-port system is not a thermal diode
-- statement:
--   Let $\kappa_c>0$, $\sigma>0$, $L>0$ and $Q_0\ne0$, let $H\in\mathbb R$, and let the channel slopes $C_1(x_a),D_1(x_a),C_2(x_a),C_1(x_b),D_2(x_b),C_2(x_b)$ satisfy the energy balance (16). Suppose the matrix $\mathbf G$ of Eq. (17) is invertible, and suppose the system is steady-state globally reciprocal, $\mathbf G_{12}=\mathbf G_{21}$. Then $\mathbf G_{11}=\mathbf G_{22}$, the flux matrix of Eq. (19) satisfies $\mathbf Q_{21}=-\mathbf Q_{12}$ and $\mathbf Q_{11}+\mathbf Q_{22}=0$, and the system is not a thermal diode. That is, for all temperatures $T_1,T_2$, if $\mathbf Gf=(T_1,T_2)^\top$ and $\mathbf G\tilde f=(T_2,T_1)^\top$, then
--
--   $$\mathbf Q\tilde f=-\begin{pmatrix}0&1\\1&0\end{pmatrix}\mathbf Qf.$$
--
--   This is the first half of the paper's equivalence (Section IV, the paragraph after Eq. (26)).
--
--   **Formalization Note** $\mathbf G$ is taken at leading order in $L$ (see the definitions). The paper calls $\mathbf Q$ "anti-symmetric and traceless". What follows from Eqs. (20) and (21) is antisymmetry of the off-diagonal part, $\mathbf Q_{21}=-\mathbf Q_{12}$, together with $\operatorname{tr}\mathbf Q=0$, and that is what is stated. The paper uses $\mathbf G^{-1}$, which is why invertibility of $\mathbf G$ is a hypothesis.
-- source:
--   Li, Li, Qi, Qiu and Chen, Diffusive non-reciprocity and thermal diode, arXiv:1912.10252v3 (2019), claim c020; Section IV, Eqs. (18)-(26) and the paragraph after Eq. (26), PDF p. 7

import Mathlib
import Definitions.Def_Arxiv1912_10252_Basic

open Matrix

namespace Arxiv1912_10252

theorem reciprocal_implies_not_diode (s : TwoPortData) (hkc : 0 < s.kc) (hsigma : 0 < s.sigma)
    (hL : 0 < s.L) (hQ0 : s.Q0 ≠ 0) (hE : EnergyConservation s) (hG : (greenMat s).det ≠ 0)
    (hrec : IsGloballyReciprocal s) :
    greenMat s 0 0 = greenMat s 1 1 ∧
    fluxMat s 1 0 = -fluxMat s 0 1 ∧
    fluxMat s 0 0 + fluxMat s 1 1 = 0 ∧
    IsNotDiode s := by sorry

end Arxiv1912_10252
