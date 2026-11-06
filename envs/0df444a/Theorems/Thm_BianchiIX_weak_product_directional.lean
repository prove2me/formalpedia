-- Prove2me | Theorems.Thm_BianchiIX_weak_product_directional
-- name    : BianchiIX.weak_product_directional
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T21:04:59.112919+00:00
-- url     : https://prove2.me/theorems/f741bec2-ad55-4a59-831d-e999192c5bf0
-- title:
--   The directional evolution of the two-wall product
-- statement:
--   For $y=(m,u,v,w)\in\mathbb R^4$, define
--   $$K(u,v,w)=u^2+v^2+w^2-2(uv+vw+wu),\qquad \kappa=u(v+w-u),$$
--   $$F_m=-v^2+w^2+u(v-w)-m\kappa,\qquad
--   F_u=\tfrac12(1-m^2-(v-w)^2+u^2)u,$$
--   $$F_v=(m-1-\kappa)v,\qquad F_w=(-m-1-\kappa)w,\qquad
--   F=(F_m,F_u,F_v,F_w),$$
--   and $E(m,v)=(m-1)^2+v^2$.
--   For every projective state,
--   $$F_vw+vF_w=-2(1+\kappa)vw.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/Projective.lean#L23-L27

import Definitions.Def_BianchiIX_Algebra_Projective
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open BianchiIX
noncomputable section

theorem BianchiIX.weak_product_directional (m u v w : ℝ) :
    activeVelocity m u v w * w + v * weakVelocity m u v w =
      -2 * (1 + coupling u v w) * (v * w) := by sorry
