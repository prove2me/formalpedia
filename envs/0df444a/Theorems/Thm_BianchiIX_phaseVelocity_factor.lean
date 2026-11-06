-- Prove2me | Theorems.Thm_BianchiIX_phaseVelocity_factor
-- name    : BianchiIX.phaseVelocity_factor
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T21:04:58.661587+00:00
-- url     : https://prove2.me/theorems/86f78f3e-cc5e-4148-bf52-8b947d5f6ace
-- title:
--   Factorization of the projective phase velocity
-- statement:
--   For $y=(m,u,v,w)\in\mathbb R^4$, define
--   $$K(u,v,w)=u^2+v^2+w^2-2(uv+vw+wu),\qquad \kappa=u(v+w-u),$$
--   $$F_m=-v^2+w^2+u(v-w)-m\kappa,\qquad
--   F_u=\tfrac12(1-m^2-(v-w)^2+u^2)u,$$
--   $$F_v=(m-1-\kappa)v,\qquad F_w=(-m-1-\kappa)w,\qquad
--   F=(F_m,F_u,F_v,F_w),$$
--   and $E(m,v)=(m-1)^2+v^2$.
--   For all real $m,u,v,w$,
--   $$F_m=-(v+w-u)(v-w+mu).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/Projective.lean#L18-L21

import Definitions.Def_BianchiIX_Algebra_Projective
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open BianchiIX
noncomputable section

theorem BianchiIX.phaseVelocity_factor (m u v w : ℝ) :
    phaseVelocity m u v w = -(v + w - u) * (v - w + m * u) := by sorry
