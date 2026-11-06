-- Prove2me | Theorems.Thm_BianchiIX_terminal_phase_composition_bounds
-- name    : BianchiIX.terminal_phase_composition_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T06:48:17.015466+00:00
-- url     : https://prove2.me/theorems/5e6a963c-14a7-4fbc-92c1-7fe5a40bf474
-- title:
--   The terminal phase chain rule preserves the small growing-wall factor
-- statement:
--   Let $0<\alpha\leq1$, $A,B,u\geq0$, $0\leq v,w\leq1$,
--   and real triples $p,q,r,s$. For $j=0,1,2$, assume
--   $$|p_j|\leq B/\alpha^2,\quad |q_j|,|r_j|,|s_j|\leq B/\alpha,$$
--   $$|B_u|,|B_v|\leq B/\alpha^2,\quad |L_r|\leq Auv,\quad
--   |L_u|\leq A\alpha v,\quad |L_v|\leq Au,\quad |L_w|\leq A\alpha uv.$$
--   Set $D_j=L_rp_j+L_u u q_j+L_v v r_j+L_w w s_j$. Then
--   $$|D_0|+|D_1+L_wB_u|\leq10ABuv/\alpha^2,\qquad
--   |D_2+L_vB_v|\leq10ABu/\alpha^2,$$
--   $$|L_vB_v|\leq ABu/\alpha^2,\qquad |L_wB_u|\leq ABuv/\alpha.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/TerminalPhaseComposition.lean#L9-L84

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace BianchiIX
end BianchiIX

open BianchiIX

theorem BianchiIX.terminal_phase_composition_bounds {α A B u v w Lr Lu Lv Lw Bu Bv : ℝ}
    (p q r s : Fin 3 → ℝ) (hα : 0 < α ∧ α ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hu : 0 ≤ u) (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1)
    (hp : ∀ j, |p j| ≤ B / α ^ 2) (hq : ∀ j, |q j| ≤ B / α)
    (hr : ∀ j, |r j| ≤ B / α) (hs : ∀ j, |s j| ≤ B / α)
    (hBu : |Bu| ≤ B / α ^ 2) (hBv : |Bv| ≤ B / α ^ 2)
    (hLr : |Lr| ≤ A * u * v) (hLu : |Lu| ≤ A * α * v)
    (hLv : |Lv| ≤ A * u) (hLw : |Lw| ≤ A * α * u * v) :
    let D := fun j => Lr * p j + Lu * (u * q j) + Lv * (v * r j) + Lw * (w * s j)
    |D 0| + |D 1 + Lw * Bu| ≤ 10 * A * B * u * v / α ^ 2 ∧
      |D 2 + Lv * Bv| ≤ 10 * A * B * u / α ^ 2 ∧
      |Lv * Bv| ≤ A * B * u / α ^ 2 ∧ |Lw * Bu| ≤ A * B * u * v / α := by sorry
