-- Prove2me | Theorems.Thm_BianchiIX_normalized_wall_formula
-- name    : BianchiIX.normalized_wall_formula
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T15:27:34.714201+00:00
-- url     : https://prove2.me/theorems/7862bb76-3c87-4d5e-8056-53f2c8942b98
-- title:
--   Exponential integral formula for the curvature walls
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
--   Let $I$ be an open convex subset of $\mathbb R$, and let
--   $\alpha'=F\circ\alpha$ on $I$. For $t_0,t\in I$ and $i\in\{1,2,3\}$,
--   $$N_i(\alpha(t))=N_i(\alpha(t_0))\exp\left(\int_{t_0}^t r_i(\alpha(u))\,du\right).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/WallEvolution.lean#L56-L62

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

theorem BianchiIX.normalized_wall_formula {I : Set ℝ} (hI : Convex ℝ I) (hopen : IsOpen I)
    {α : ℝ → NormalizedState} (hα : ∀ t ∈ I, HasDerivAt α (normalizedField (α t)) t)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ I) (ht : t ∈ I) (i : Fin 3) :
    wallValue i (α t) = wallValue i (α t₀) * Real.exp (∫ u in t₀..t, wallRate i (α u)) := by sorry
