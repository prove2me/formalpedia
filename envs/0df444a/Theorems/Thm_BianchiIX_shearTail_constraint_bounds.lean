-- Prove2me | Theorems.Thm_BianchiIX_shearTail_constraint_bounds
-- name    : BianchiIX.shearTail_constraint_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T07:03:33.508204+00:00
-- url     : https://prove2.me/theorems/addda508-bb34-4319-92be-3b352d60a85f
-- title:
--   The shear tail constraint gives a quadratic projection denominator
-- statement:
--   Write $K(n,x,y)=n^2+x^2+y^2-2(nx+xy+ny)$.
--   Suppose $0<a\leq1/256$, $p<0$, $a/2\leq s\leq3a$,
--   $0\leq n,x\leq a^2$, $0\leq y\leq a/16$, and
--   $p^2+s^2+K(n,x,y)=1$. Then
--   $$|K(n,x,y)|\leq a^2/128,\qquad
--   a^2/5\leq1-p^2\leq10a^2,$$
--   $$-1<p\leq-15/16,\qquad a^2/10\leq1+p\leq6a^2.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/ShearTailBounds.lean#L7-L36

import Definitions.Def_BianchiIX_Algebra_Flow
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp

noncomputable section
open BianchiIX

theorem BianchiIX.shearTail_constraint_bounds {a p s n x y : ℝ}
    (ha : 0 < a ∧ a ≤ 1 / 256) (hp : p < 0)
    (hs : a / 2 ≤ s ∧ s ≤ 3 * a)
    (hn : 0 ≤ n ∧ n ≤ a ^ 2) (hx : 0 ≤ x ∧ x ≤ a ^ 2)
    (hy : 0 ≤ y ∧ y ≤ a / 16) (hc : constraint p s n x y = 1) :
    |curvature n x y| ≤ a ^ 2 / 128 ∧
      a ^ 2 / 5 ≤ 1 - p ^ 2 ∧ 1 - p ^ 2 ≤ 10 * a ^ 2 ∧
      -1 < p ∧ p ≤ -(15 / 16) ∧
      a ^ 2 / 10 ≤ 1 + p ∧ 1 + p ≤ 6 * a ^ 2 := by sorry
