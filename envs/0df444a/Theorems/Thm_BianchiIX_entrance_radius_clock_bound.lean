-- Prove2me | Theorems.Thm_BianchiIX_entrance_radius_clock_bound
-- name    : BianchiIX.entrance_radius_clock_bound
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T07:48:10.793641+00:00
-- url     : https://prove2.me/theorems/7e391a4c-ae8c-46c3-9108-b64849c31d92
-- title:
--   Entrance radial drift preserves the weak wall square over the radius
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
--   Assume $k\geq7/4$, $m\geq1$,
--   $|r(m,v)-k|\leq k/100$, $0\leq u,w\leq1/10000$, and $0<v\leq1$.
--   Writing $R=r(m,v)$, one has
--   $$\left|\frac{-cR+(m-1)(u-w)^2/R}{s(m,u,v,w)}\right|
--   \leq4\bigl(u(v+w)+u^2+w^2/k\bigr).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/EntranceRadialBounds.lean#L7-L60

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Algebra_ConnectionBounds
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

theorem BianchiIX.entrance_radius_clock_bound {k m u v w : ℝ} (hk : 7 / 4 ≤ k) (hm : 1 ≤ m)
    (hr : |coreRadius m v - k| ≤ k / 100)
    (hu : 0 ≤ u ∧ u ≤ 1 / 10000) (hv : 0 < v ∧ v ≤ 1)
    (hw : 0 ≤ w ∧ w ≤ 1 / 10000) :
    |(-coupling u v w * coreRadius m v + (m - 1) / coreRadius m v * (u - w) ^ 2) /
      connectionSpeed m u v w| ≤ 4 * (u * (v + w) + u ^ 2 + w ^ 2 / k) := by sorry
