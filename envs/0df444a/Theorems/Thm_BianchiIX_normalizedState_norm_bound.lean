-- Prove2me | Theorems.Thm_BianchiIX_normalizedState_norm_bound
-- name    : BianchiIX.normalizedState_norm_bound
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T15:28:56.209794+00:00
-- url     : https://prove2.me/theorems/955f0d3f-a5d8-47cc-a18d-6cb8a02c2bfa
-- title:
--   A state bound from its constraint and curvature walls
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
--   Let $X=\mathbb R^5$ with coordinates $x=(p,s,a,b,c)$ and the sup norm. Write
--   $$F(x)=(P,Q,r_1a,r_2b,r_3c),\qquad \mathcal C(x)=C(p,s,a,b,c),$$
--   and let $W=\{(p,s,a,b,c)\in X:a>0,\ b>0,\ c>0\}$.
--
--   If $x\in W$, $\mathcal C(x)=1$, and $N_i(x)\leq M$ for all three walls,
--   then $\|x\|\leq1+3M$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/WallEvolution.lean#L95-L139

import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
open BianchiIX
open Set MeasureTheory

theorem BianchiIX.normalizedState_norm_bound {x : NormalizedState} {M : ℝ}
    (hpos : positiveWalls x) (hcon : stateConstraint x = 1)
    (hwall : ∀ i : Fin 3, wallValue i x ≤ M) : ‖x‖ ≤ 1 + 3 * M := by sorry
