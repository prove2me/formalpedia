-- Prove2me | Theorems.Thm_BianchiIX_normalized_solution_unique
-- name    : BianchiIX.normalized_solution_unique
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T15:35:58.758846+00:00
-- url     : https://prove2.me/theorems/38a37bda-f22c-4fad-b179-d4b6cf55de6a
-- title:
--   Uniqueness on a convex time domain
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
--   Let $I\subset\mathbb R$ be convex. If $\alpha'=F\circ\alpha$ and
--   $\beta'=F\circ\beta$ on $I$, $t_0\in I$, and $\alpha(t_0)=\beta(t_0)$,
--   then $\alpha=\beta$ on $I$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/LocalFlow.lean#L48-L56

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

theorem BianchiIX.normalized_solution_unique {I : Set ℝ} (hI : Convex ℝ I)
    {α β : ℝ → NormalizedState} {t₀ : ℝ}
    (hα : ∀ t ∈ I, HasDerivAt α (normalizedField (α t)) t)
    (hβ : ∀ t ∈ I, HasDerivAt β (normalizedField (β t)) t)
    (ht₀ : t₀ ∈ I) (heq : α t₀ = β t₀) : EqOn α β I := by sorry
