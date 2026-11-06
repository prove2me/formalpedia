-- Prove2me | Theorems.Thm_BianchiIX_normalized_constraint_constant
-- name    : BianchiIX.normalized_constraint_constant
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T14:00:51.910349+00:00
-- url     : https://prove2.me/theorems/b226fdd8-67a6-4eac-97d5-7e3d030c6bd1
-- title:
--   Constraint conservation on every interval of a normalized trajectory
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
--   Let $I\subset\mathbb R$ be convex and let $\alpha:\mathbb R\to X$ have
--   derivative $F(\alpha(t))$ at every $t\in I$. For any $t_0,t\in I$,
--   $$\mathcal C(\alpha(t))=\mathcal C(\alpha(t_0)).$$
--   Thus the constraint has a constant value along each such trajectory interval.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/Normalized.lean#L61-L68

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

theorem BianchiIX.normalized_constraint_constant {I : Set ℝ} (hI : Convex ℝ I)
    {α : ℝ → NormalizedState} (hα : ∀ t ∈ I, HasDerivAt α (normalizedField (α t)) t)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ I) (ht : t ∈ I) :
    stateConstraint (α t) = stateConstraint (α t₀) := by sorry
