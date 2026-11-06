-- Prove2me | Theorems.Thm_BianchiIX_curvature_lower_bound
-- name    : BianchiIX.curvature_lower_bound
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T05:36:40.537301+00:00
-- url     : https://prove2.me/theorems/bdf828e5-cb1f-4718-9c93-99a2852efa43
-- title:
--   A sharp lower bound for curvature in terms of the wall product
-- statement:
--   For real variables $p,s,a,b,c$, set
--   $$K=a^2+b^2+c^2-2(ab+bc+ca),\qquad S=p^2+s^2,\qquad C=S+K.$$
--   The shear components and wall rates are
--   $$P=Kp-2a^2+b^2+c^2+ab-2bc+ac,$$
--   $$Q=Ks+\sqrt{3}(-b^2+c^2+ab-ac),$$
--   $$r_1=-S+2p,\qquad r_2=-S-p+\sqrt{3}s,\qquad r_3=-S-p-\sqrt{3}s.$$
--   These functions define the normalized vacuum Bianchi IX vector field
--   $(P,Q,r_1a,r_2b,r_3c)$.
--   For $a,b,c>0$ and $r\in\mathbb R$ with $r^3=abc$,
--   $$K(a,b,c)\geq-3r^2.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/Flux.lean#L51-L85

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Algebra_Flux
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp

open BianchiIX
noncomputable section

theorem BianchiIX.curvature_lower_bound
    {a b c r : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hr : r ^ 3 = a * b * c) : -3 * r ^ 2 ≤ curvature a b c := by sorry
