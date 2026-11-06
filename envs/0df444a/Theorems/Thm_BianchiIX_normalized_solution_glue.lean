-- Prove2me | Theorems.Thm_BianchiIX_normalized_solution_glue
-- name    : BianchiIX.normalized_solution_glue
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T15:38:46.187696+00:00
-- url     : https://prove2.me/theorems/d6a0f343-2fbb-4ac8-884f-bf24f1d829f2
-- title:
--   Gluing exact normalized solutions on overlapping intervals
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
--   Let $I,J\subset\mathbb R$ be open and convex. Suppose $\alpha'=F\circ\alpha$
--   on $I$, $\beta'=F\circ\beta$ on $J$, and $\alpha(s)=\beta(s)$ at some
--   $s\in I\cap J$. Then there exists $\gamma:\mathbb R\to X$ agreeing with
--   $\alpha$ on $I$ and with $\beta$ on $J$, and satisfying
--   $\gamma'=F\circ\gamma$ on $I\cup J$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/Continuation.lean#L58-L84

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
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique

noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology NNReal

theorem BianchiIX.normalized_solution_glue {I J : Set ℝ}
    (hI : Convex ℝ I) (hoI : IsOpen I) (hJ : Convex ℝ J) (hoJ : IsOpen J)
    {α β : ℝ → NormalizedState}
    (hα : ∀ t ∈ I, HasDerivAt α (normalizedField (α t)) t)
    (hβ : ∀ t ∈ J, HasDerivAt β (normalizedField (β t)) t)
    {s : ℝ} (hsI : s ∈ I) (hsJ : s ∈ J) (heq : α s = β s) :
    ∃ γ : ℝ → NormalizedState, EqOn γ α I ∧ EqOn γ β J ∧
      ∀ t ∈ I ∪ J, HasDerivAt γ (normalizedField (γ t)) t := by sorry
