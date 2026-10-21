-- Prove2me | Theorems.Thm_DerivativeChainPrivate_row10_branch_exists_2
-- name    : DerivativeChainPrivate.row10_branch_exists_2
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-20T22:25:31.384395+00:00
-- url     : https://prove2.me/theorems/fbfb459f-7444-4750-9559-10f0ca385267
-- title:
--   Certified analytic branch 2 of the tenth-row inverse cubic
-- statement:
--   Let $\alpha\in\mathbb R$ lie in the exact dyadic interval stated formally (near $2.465888999$) and satisfy
--   $$\alpha^3=\frac{1001}{20}-66\alpha+21\alpha^2.$$
--   Let $P_\alpha$ be the explicit Newton approximant for the tenth-row inverse cubic
--   $$G_{10}(t,v)=-60v^3+(1260-630t+30t^2)v^2+(-3960+5040t-1680t^2+120t^3)v+3003-6435t+4620t^2-1260t^3+105t^4-t^5.$$
--   There exists $Y:\mathbb C\to\mathbb C$, holomorphic on $|t|<2$, such that
--   $$|Y(t)|\le10^{-14}\quad(|t|\le2),\qquad Y(t)\in\mathbb R\quad(t\in[-2,2]),$$
--   and, for every $|t|\le2$,
--   $$G_{10}(t,P_\alpha(t)+t^{32}Y(t))=0.$$
--   This supplies one analytic branch for the complete inverse-root cover used in the tenth-row compatible selection.
-- source:
--   https://gist.github.com/Amal-David/adce933460b7501cb123f483f62775eb/f5a76eda649f3e995a8ec6b98387b23b64c6debb#file-fifth-md; https://gist.github.com/Amal-David/adce933460b7501cb123f483f62775eb/f5a76eda649f3e995a8ec6b98387b23b64c6debb#file-fifth-md; upper/H5_UPPER_BRIDGE.md, row-10 inverse cubic. The exact intervals and coefficient certificates are part of the accompanying Lean formalization.

import Definitions.Def_DerivativeChainPrivate_fifth_row10_coefficient_bounds
import Definitions.Def_DerivativeChainPrivate_fifth_row10_inverse_residual
import Definitions.Def_DerivativeChainPrivate_fifth_row10_newton_polynomials
import Definitions.Def_DerivativeChainPrivate_fifth_row10_residual
import Mathlib
import Theorems.Thm_DerivativeChainPrivate_row10_newton_inverse
import Theorems.Thm_DerivativeChainPrivate_row10_newton_residual
open Polynomial MeasureTheory Filter Set DerivativeChainPrivate
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.row10_branch_exists_2 (α : ℝ)
    (hlo : (97160973648365359300573924314704264662030400264262134485861186056383350158245991701430729829643120229512794018619323/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ α) (hhi : α ≤ (24290243412091339825143481078676066165507600066065533621465296514095837539561497925357682457410780057378198504654831/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ))
    (hα : α^3=(1001/20)+(-66)*α+(21)*α^2) :
    ∃ Y : ℂ → ℂ, DifferentiableOn ℂ Y (Metric.ball 0 2) ∧
      (∀ t : ℂ, ‖t‖ ≤ 2 → ‖Y t‖ ≤ 1/100000000000000 ∧
        row10G0 t+row10G1 t*(row10P α t+t^32*Y t)+row10G2 t*(row10P α t+t^32*Y t)^2+
          (-60)*(row10P α t+t^32*Y t)^3=0) ∧
      ∀ x : ℝ, |x| ≤ 2 → (Y (x:ℂ)).im=0 := by sorry
