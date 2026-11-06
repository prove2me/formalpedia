-- Prove2me | Theorems.Thm_BianchiIX_wall_rates_le_one
-- name    : BianchiIX.wall_rates_le_one
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T13:04:52.481198+00:00
-- url     : https://prove2.me/theorems/c623d0f3-4183-4f1c-b737-f1108c887419
-- title:
--   Uniform upper bound for the three wall rates
-- statement:
--   For real variables $p,s,a,b,c$, set
--   $$K=a^2+b^2+c^2-2(ab+bc+ca),\qquad S=p^2+s^2,\qquad C=S+K.$$
--   The shear components and wall rates are
--   $$P=Kp-2a^2+b^2+c^2+ab-2bc+ac,$$
--   $$Q=Ks+\sqrt{3}(-b^2+c^2+ab-ac),$$
--   $$r_1=-S+2p,\qquad r_2=-S-p+\sqrt{3}s,\qquad r_3=-S-p-\sqrt{3}s.$$
--   These functions define the normalized vacuum Bianchi IX vector field
--   $(P,Q,r_1a,r_2b,r_3c)$.
--
--   For every $p,s\in\mathbb R$,
--   $$r_1(p,s)\leq1,\qquad r_2(p,s)\leq1,\qquad r_3(p,s)\leq1.$$
--   These pointwise estimates bound each logarithmic wall growth rate.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/Flow.lean#L91-L96

import Definitions.Def_BianchiIX_Algebra_Flow
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open BianchiIX
noncomputable section

theorem BianchiIX.wall_rates_le_one (p s : ℝ) :
    rateOne p s ≤ 1 ∧ rateTwo p s ≤ 1 ∧ rateThree p s ≤ 1 := by sorry
