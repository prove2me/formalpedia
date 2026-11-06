-- Prove2me | Theorems.Thm_BianchiIX_hasDerivAt_normalized_components
-- name    : BianchiIX.hasDerivAt_normalized_components
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T13:57:45.372947+00:00
-- url     : https://prove2.me/theorems/677f67bc-8c2e-4251-bd9a-ca667a56b70f
-- title:
--   Coordinate equations for a normalized Bianchi IX trajectory
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
--   Let $\alpha:\mathbb R\to X$, write $\alpha=(p,s,a,b,c)$, and fix a time $t$.
--   If $\alpha$ has derivative $F(\alpha(t))$ at $t$, then all five coordinate
--   derivatives exist there and satisfy
--   $$p'(t)=P(\alpha(t)),\quad s'(t)=Q(\alpha(t)),$$
--   $$a'(t)=r_1(p(t),s(t))a(t),\quad
--   b'(t)=r_2(p(t),s(t))b(t),\quad
--   c'(t)=r_3(p(t),s(t))c(t).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/Normalized.lean#L45-L53

import Definitions.Def_BianchiIX_Dynamics_Normalized
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

noncomputable section
open BianchiIX
open Set

theorem BianchiIX.hasDerivAt_normalized_components {α : ℝ → NormalizedState} {t : ℝ}
    (hα : HasDerivAt α (normalizedField (α t)) t) :
    HasDerivAt (fun u => α u 0) (shearPlus (α t 0) (α t 2) (α t 3) (α t 4)) t ∧
    HasDerivAt (fun u => α u 1) (shearMinus (α t 1) (α t 2) (α t 3) (α t 4)) t ∧
    HasDerivAt (fun u => α u 2) (rateOne (α t 0) (α t 1) * α t 2) t ∧
    HasDerivAt (fun u => α u 3) (rateTwo (α t 0) (α t 1) * α t 3) t ∧
    HasDerivAt (fun u => α u 4) (rateThree (α t 0) (α t 1) * α t 4) t := by sorry
