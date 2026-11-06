-- Prove2me | Theorems.Thm_BianchiIX_exitTail_boundary_rate_small
-- name    : BianchiIX.exitTail_boundary_rate_small
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T17:55:49.998498+00:00
-- url     : https://prove2.me/theorems/bcb3b691-4b45-4eb4-8893-6be58ebda9e7
-- title:
--   Integrably small boundary rates near the terminal radius
-- statement:
--   For $y=(m,u,v,w)\in\mathbb R^4$, define
--   $$K(u,v,w)=u^2+v^2+w^2-2(uv+vw+wu),\qquad \kappa=u(v+w-u),$$
--   $$F_m=-v^2+w^2+u(v-w)-m\kappa,\qquad
--   F_u=\tfrac12(1-m^2-(v-w)^2+u^2)u,$$
--   $$F_v=(m-1-\kappa)v,\qquad F_w=(-m-1-\kappa)w,\qquad
--   F=(F_m,F_u,F_v,F_w),$$
--   and $E(m,v)=(m-1)^2+v^2$.
--
--   Write $r(m,v)=\sqrt{(m-1)^2+v^2}$ and define
--   $$g(R,v)=\sqrt{R^2-v^2},\qquad d(R,u,v,w)=g(R,v)+u(v+w-u),$$
--   $$f_R=\frac{-u(v+w-u)R-g(R,v)(u-w)^2/R}{d},$$
--   $$a_s=\frac{2g(R,v)-R^2+2vw-w^2+u^2}{2d},\qquad
--   a_w=\frac{g(R,v)-2-u(v+w-u)}d.$$
--   The exit clock rate is $\omega(y)=1-m+u(v+w-u)$, and its field is
--   $F_{\log}(y)=F(y)/\omega(y)$. Division and square roots have their total
--   real-valued Lean meanings.
--   For $\alpha\geq0$, $7/4\leq R\leq17/4$
--   and $0\leq v\leq1$,
--   $$|a_s(R,0,v,0)|+|a_w(R,0,v,0)|
--   \leq10(\alpha+|R-(2+2\alpha)|+v^2).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/ExitTailPerturbation.lean#L113-L161

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_TerminalConnectionData
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp

noncomputable section
open BianchiIX

theorem BianchiIX.exitTail_boundary_rate_small {R v α : ℝ} (hα : 0 ≤ α)
    (hR : 7 / 4 ≤ R ∧ R ≤ 17 / 4) (hv : 0 ≤ v ∧ v ≤ 1) :
    |exitTailStrongRate R 0 v 0| + |exitTailWeakRate R 0 v 0| ≤
      10 * (α + |R - (2 + 2 * α)| + v ^ 2) := by sorry
