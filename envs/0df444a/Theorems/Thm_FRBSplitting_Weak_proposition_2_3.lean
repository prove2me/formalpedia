-- Prove2me | Theorems.Thm_FRBSplitting_Weak_proposition_2_3
-- name    : FRBSplitting.Weak.proposition_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:42:40.957762+00:00
-- url     : https://prove2.me/theorems/b8626b61-afc6-49d1-84d2-943b62b4ce55
-- title:
--   Proposition 2.3, p. 5 — the basic inequality (19) for d₂ = J_F(d₁ − u₁ − (v₁ − u₀))
-- statement:
--   Let $H$ be a real inner product space and $F:H\rightrightarrows H$ monotone, with resolvent $J_F=(I+F)^{-1}$. Let $d_1,v_2,u_1,v_1,u_0\in H$ be arbitrary and define
--
--   $$d_2=J_F\big(d_1-u_1-(v_1-u_0)\big).$$
--
--   Then for every $x\in H$ and every $u$ with $-u\in F(x)$,
--
--   $$\|d_2-x\|^2+2\langle v_2-u_1,x-d_2\rangle\le\|d_1-x\|^2+2\langle v_1-u_0,x-d_1\rangle+2\langle v_1-u_0,d_1-d_2\rangle-\|d_1-d_2\|^2-2\langle v_2-u,d_2-x\rangle.$$
--
--   Applied with $F=\lambda_kA$ it is the one-step inequality behind the analysis of the forward-reflected-backward method: the first line suggests the telescoping terms.
--
--   **Formalization Note.** The paper assumes $F$ maximally monotone; its proof uses only monotonicity, maximality serving to make $J_F$ everywhere defined and single-valued. Here $J_F$ is a given map with $w-J_F(w)\in F(J_F(w))$ for all $w$, and $F$ is only assumed monotone, which is a stronger statement. $d_2$ is a variable together with the equation $d_2=J_F(d_1-u_1-(v_1-u_0))$.
-- source:
--   Malitsky & Tam, A Forward-Backward Splitting Method for Monotone Inclusions Without Cocoercivity, arXiv:1808.04162v4, p. 5, Proposition 2.3, (18)–(19)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_FRBSplitting_Weak_Setting
open InnerProductSpace ThreeOpSplitting.Accel

namespace FRBSplitting.Weak

theorem proposition_2_3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (F : H → Set H) (hF : IsMonotoneOp F) (JF : H → H) (hJF : IsResolvent 1 F JF)
    (d1 v2 u1 v1 u0 d2 : H) (hd2 : d2 = JF (d1 - u1 - (v1 - u0)))
    (x u : H) (hu : -u ∈ F x) :
    ‖d2 - x‖ ^ 2 + 2 * ⟪v2 - u1, x - d2⟫_ℝ
      ≤ ‖d1 - x‖ ^ 2 + 2 * ⟪v1 - u0, x - d1⟫_ℝ
        + 2 * ⟪v1 - u0, d1 - d2⟫_ℝ - ‖d1 - d2‖ ^ 2 - 2 * ⟪v2 - u, d2 - x⟫_ℝ := by sorry

end FRBSplitting.Weak
