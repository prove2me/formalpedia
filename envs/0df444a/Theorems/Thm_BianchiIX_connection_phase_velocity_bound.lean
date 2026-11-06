-- Prove2me | Theorems.Thm_BianchiIX_connection_phase_velocity_bound
-- name    : BianchiIX.connection_phase_velocity_bound
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T07:44:23.576447+00:00
-- url     : https://prove2.me/theorems/704fc142-3a60-4179-8e75-b29dfd1966ae
-- title:
--   Connection phase velocity is bounded by wall squares and strong amplitude
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
--
--   Assume $\mu\geq4$, $|m-\mu|\leq1/2$, $0\leq u\leq1/10000$,
--   and $0\leq v,w\leq1$.
--   If also $u\leq v$, then
--   $$|F_m(-m,u,v,w)|\leq v^2+w^2+3\mu u.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/ConnectionBounds.lean#L105-L120

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

noncomputable section
open BianchiIX

theorem BianchiIX.connection_phase_velocity_bound {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) (huv : u ≤ v) :
    |phaseVelocity (-m) u v w| ≤ v ^ 2 + w ^ 2 + 3 * μ * u := by sorry
