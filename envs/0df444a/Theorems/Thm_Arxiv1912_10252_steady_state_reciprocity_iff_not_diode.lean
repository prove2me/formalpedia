-- Prove2me | Theorems.Thm_Arxiv1912_10252_steady_state_reciprocity_iff_not_diode
-- name    : Arxiv1912_10252.steady_state_reciprocity_iff_not_diode
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T07:28:50.63149+00:00
-- url     : https://prove2.me/theorems/460f4289-92bb-4460-a5d9-38c42417022f
-- title:
--   Section IV: steady-state global reciprocity is equivalent to the absence of the diode effect
-- statement:
--   Let $\kappa_c>0$, $\sigma>0$, $L>0$ and $Q_0\ne0$, let $H\in\mathbb R$, and let the channel slopes $C_1(x_a),D_1(x_a),C_2(x_a),C_1(x_b),D_2(x_b),C_2(x_b)$ satisfy the energy balance (16). Suppose the matrix $\mathbf G$ of Eq. (17) is invertible. Then the two-port system is not a thermal diode in the sense of Eq. (25) if and only if it is steady-state globally reciprocal:
--
--   $$\Big(\forall T_1,T_2:\ \mathbf Gf=\begin{pmatrix}T_1\\T_2\end{pmatrix},\ \mathbf G\tilde f=\begin{pmatrix}T_2\\T_1\end{pmatrix}\ \Longrightarrow\ \mathbf Q\tilde f=-\begin{pmatrix}0&1\\1&0\end{pmatrix}\mathbf Qf\Big)\iff \mathbf G_{12}=\mathbf G_{21}.$$
--
--   Equivalently, a two-port system with broken steady-state global reciprocity is a thermal diode, and conversely. This is the central result of the paper (Abstract, Section IV and Section VI). It is stated in the paper's channel model, in which the heat generation $H$ in $V$ is independent of the conditions outside $V$.
--
--   **Formalization Note** $\mathbf G$ is taken at leading order as $L\to\infty$ (see the definitions), which is where the paper states the equivalence. The paper assumes $Q_0\ne0$ implicitly; without it every system with invertible $\mathbf G$ satisfies Eq. (25), including non-reciprocal ones, and the equivalence fails. The case $H=0$, for which the paper says the result is "similarly obtained", is included, because the no-diode condition does not use $\mathbf Q^{-1}$.
-- source:
--   Li, Li, Qi, Qiu and Chen, Diffusive non-reciprocity and thermal diode, arXiv:1912.10252v3 (2019), claim c020; Section IV, Eqs. (15)-(27), PDF pp. 6-7; also Abstract and Section VI

import Mathlib
import Definitions.Def_Arxiv1912_10252_Basic

open Matrix

namespace Arxiv1912_10252

theorem steady_state_reciprocity_iff_not_diode (s : TwoPortData) (hkc : 0 < s.kc)
    (hsigma : 0 < s.sigma) (hL : 0 < s.L) (hQ0 : s.Q0 ≠ 0) (hE : EnergyConservation s)
    (hG : (greenMat s).det ≠ 0) :
    IsNotDiode s ↔ IsGloballyReciprocal s := by sorry

end Arxiv1912_10252
