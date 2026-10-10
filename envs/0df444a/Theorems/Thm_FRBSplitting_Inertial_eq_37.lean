-- Prove2me | Theorems.Thm_FRBSplitting_Inertial_eq_37
-- name    : FRBSplitting.Inertial.eq_37
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:44:36.914213+00:00
-- url     : https://prove2.me/theorems/d74ff30b-53e3-4943-be6f-cba3041c73e6
-- title:
--   (37), p. 12 — the form of (19) from Proposition 2.3 used in Lemma 4.2
-- statement:
--   Let $H$ be a real inner product space, $F:H\rightrightarrows H$ monotone, and $J_F=(I+F)^{-1}$ its resolvent. Let $d_1,u_1,v_1,u_0\in H$ be arbitrary and
--
--   $$d_2=J_F\big(d_1-u_1-(v_1-u_0)\big).$$
--
--   Then for every $x\in H$ and every $u$ with $u\in -F(x)$,
--
--   $$\|d_2-x\|^2+2\langle u-u_1,x-d_2\rangle\le\|d_1-x\|^2+2\langle v_1-u_0,x-d_1\rangle+2\langle v_1-u_0,d_1-d_2\rangle-\|d_1-d_2\|^2.$$
--
--   This is inequality (19) of Proposition 2.3 with $v_2=u$; it is the one-step estimate behind Lemma 4.2.
--
--   **Formalization Note.** The resolvent is a map `JF` with the hypothesis that $d-J_F(d)\in F(J_F(d))$ for every $d$. Proposition 2.3 assumes $F$ maximally monotone; only monotonicity is assumed here (the proof on p. 5 uses only monotonicity, maximality serving to make $J_F$ single-valued and everywhere defined, which the hypothesis on `JF` already provides).
-- source:
--   Malitsky & Tam, A Forward-Backward Splitting Method for Monotone Inclusions Without Cocoercivity, arXiv:1808.04162v4, p. 12, (37); p. 5, Proposition 2.3, (18)–(19)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_FRBSplitting_Inertial_Setting
open InnerProductSpace ThreeOpSplitting.Accel

namespace FRBSplitting.Inertial

theorem eq_37 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (F : H → Set H) (hF : IsMonotoneOp F) (JF : H → H) (hJF : IsResolvent 1 F JF)
    (d1 u1 v1 u0 : H) (x u : H) (hu : -u ∈ F x) :
    ‖JF (d1 - u1 - (v1 - u0)) - x‖ ^ 2 + 2 * ⟪u - u1, x - JF (d1 - u1 - (v1 - u0))⟫_ℝ ≤
      ‖d1 - x‖ ^ 2 + 2 * ⟪v1 - u0, x - d1⟫_ℝ
        + 2 * ⟪v1 - u0, d1 - JF (d1 - u1 - (v1 - u0))⟫_ℝ
        - ‖d1 - JF (d1 - u1 - (v1 - u0))‖ ^ 2 := by sorry

end FRBSplitting.Inertial
