-- Prove2me | Theorems.Thm_BianchiIX_compact_phase_composition_bounds
-- name    : BianchiIX.compact_phase_composition_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T06:48:18.242595+00:00
-- url     : https://prove2.me/theorems/976127f2-6045-4a72-bab6-6735bd166836
-- title:
--   Compact phase composition preserves the weak-wall factor
-- statement:
--   Let $A,B,x,y\geq0$ with $x+y\leq1$. Let $p,q,r\in\mathbb R^3$
--   have all components bounded in absolute value by $A$, and suppose
--   $$|B_u|,|B_v|\leq A,\quad |E|,|L_r|\leq BA^2y(x+y),\quad
--   |L_u|\leq BAy,\quad |L_v|\leq BA(x+y).$$
--   Put $D_j=L_rp_j+L_u xq_j+L_v yr_j$ and $C=BA^2(A+3)$. Then
--   $$|E|+|D_0|\leq Cy(x+y),\quad
--   |D_1+L_uB_u|\leq Cy,\quad |D_2+L_vB_v|\leq C(x+y).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/CompactPhaseComposition.lean#L8-L77

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace BianchiIX
end BianchiIX

open BianchiIX

theorem BianchiIX.compact_phase_composition_bounds {A B x y E Lr Lu Lv Bu Bv : ℝ}
    (p q r : Fin 3 → ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hb : x + y ≤ 1)
    (hp : ∀ j, |p j| ≤ A) (hq : ∀ j, |q j| ≤ A) (hr : ∀ j, |r j| ≤ A)
    (hBu : |Bu| ≤ A) (hBv : |Bv| ≤ A)
    (hE : |E| ≤ B * A ^ 2 * y * (x + y))
    (hLr : |Lr| ≤ B * A ^ 2 * y * (x + y))
    (hLu : |Lu| ≤ B * A * y) (hLv : |Lv| ≤ B * A * (x + y)) :
    let D := fun j => Lr * p j + Lu * (x * q j) + Lv * (y * r j)
    let C := B * A ^ 2 * (A + 3)
    |E| + |D 0| ≤ C * y * (x + y) ∧
      |D 1 + Lu * Bu| ≤ C * y ∧ |D 2 + Lv * Bv| ≤ C * (x + y) := by sorry
