-- Prove2me | Theorems.Thm_BianchiIX_entrance_phase_bounds
-- name    : BianchiIX.entrance_phase_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T07:44:33.226784+00:00
-- url     : https://prove2.me/theorems/f1ccda8d-0a97-47dc-b49a-8828fffaaca2
-- title:
--   A narrow entrance radius band controls the phase gap
-- statement:
--   For $y=(m,u,v,w)\in\mathbb R^4$, define
--   $$K(u,v,w)=u^2+v^2+w^2-2(uv+vw+wu),\qquad \kappa=u(v+w-u),$$
--   $$F_m=-v^2+w^2+u(v-w)-m\kappa,\qquad
--   F_u=\tfrac12(1-m^2-(v-w)^2+u^2)u,$$
--   $$F_v=(m-1-\kappa)v,\qquad F_w=(-m-1-\kappa)w,\qquad
--   F=(F_m,F_u,F_v,F_w),$$
--   and $E(m,v)=(m-1)^2+v^2$.
--
--   Put $c=u(v+w-u)$, $s(m,u,v,w)=m-1-c$,
--   $b(m,u,v,w)=(1-m^2-(v-w)^2+u^2)/2$,
--   $D(m,u,v,w)=3+m^2+K(u,v,w)$, and $r(m,v)=\sqrt{(m-1)^2+v^2}$.
--   If $k\geq7/4$, $m\geq1$,
--   $|r(m,v)-k|\leq k/100$ and $0\leq v\leq1$, then
--   $$4k/5\leq m-1\leq101k/100.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/EntranceBounds.lean#L8-L27

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
open BianchiIX

theorem BianchiIX.entrance_phase_bounds {k m v : ℝ} (hk : 7 / 4 ≤ k) (hm : 1 ≤ m)
    (hr : |coreRadius m v - k| ≤ k / 100) (hv : 0 ≤ v ∧ v ≤ 1) :
    4 / 5 * k ≤ m - 1 ∧ m - 1 ≤ 101 / 100 * k := by sorry
