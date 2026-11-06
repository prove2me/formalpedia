-- Prove2me | Theorems.Thm_BianchiIX_exists_normalized_solution_uniform
-- name    : BianchiIX.exists_normalized_solution_uniform
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T15:31:46.753664+00:00
-- url     : https://prove2.me/theorems/1484b199-2a6e-4d5a-8423-64a49c07fb97
-- title:
--   Uniform local existence time for bounded initial data
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
--   For each $R\geq0$ there is $\varepsilon>0$ such that for every $\|x\|\leq R$
--   and every $t_0\in\mathbb R$ there is a curve $\alpha$ with $\alpha(t_0)=x$
--   and $\alpha'=F\circ\alpha$ on $(t_0-\varepsilon,t_0+\varepsilon)$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/Continuation.lean#L10-L41

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

theorem BianchiIX.exists_normalized_solution_uniform (R : ℝ) (hR : 0 ≤ R) :
    ∃ ε > (0 : ℝ), ∀ x : NormalizedState, ‖x‖ ≤ R → ∀ t₀ : ℝ,
      ∃ α : ℝ → NormalizedState, α t₀ = x ∧
        ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (normalizedField (α t)) t := by sorry
