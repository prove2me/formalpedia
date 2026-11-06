-- Prove2me | Theorems.Thm_BianchiIX_exists_normalizedMaxCurve_local_derivative
-- name    : BianchiIX.exists_normalizedMaxCurve_local_derivative
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T22:22:01.782634+00:00
-- url     : https://prove2.me/theorems/59011feb-b842-406f-8864-6a601f57b39a
-- title:
--   The variational family is the actual initial-state derivative
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
--   Write $N_1(x)=a$, $N_2(x)=b$, and $N_3(x)=c$. For initial data $(x_0,t_0)$,
--   let $I_{\max}(x_0,t_0)$ be the union of all open convex domains of solutions
--   with these initial data, and let $\alpha_{x_0,t_0}$ be their compatible curve.
--   A solution $S$ has such a domain $I_S$, a curve $\alpha_S$, and
--   $\alpha_S(t_0)=x_0$.
--
--   Let $\mathcal L(X,X)$ be the continuous linear operators on $X$ and set
--   $$A(x)=dF_x,\qquad \widetilde F(x,J)=(F(x),A(x)\circ J).$$
--   For every $(x_0,t_0)$ there are
--   $r,\varepsilon>0$ and an operator-valued map $J(x,t)$ such that,
--   on $U=B(x_0,r)\times I$ with $I=(t_0-\varepsilon,t_0+\varepsilon)$,
--   both $(x,t)\mapsto\alpha_{x,t_0}(t)$ and $J$ are continuous.
--   For every $x\in B(x_0,r)$, one has $I\subset I_{\max}(x,t_0)$,
--   $J(x,t_0)=\operatorname{id}_X$, and for $t\in I$,
--   $$d_x\alpha_{x,t_0}(t)=J(x,t),\qquad
--   \partial_tJ(x,t)=A(\alpha_{x,t_0}(t))\circ J(x,t).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/InitialDerivative.lean#L10-L79

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_Linearization
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
open Set Filter Metric Asymptotics
open scoped Topology NNReal

theorem BianchiIX.exists_normalizedMaxCurve_local_derivative (x₀ : NormalizedState) (t₀ : ℝ) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ J : NormalizedState × ℝ → NormalizedVariation,
      ContinuousOn (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2)
        (ball x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)) ∧
      ContinuousOn J (ball x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)) ∧
      ∀ x ∈ ball x₀ r,
        Ioo (t₀ - ε) (t₀ + ε) ⊆ normalizedMaxDomain x t₀ ∧
        J (x, t₀) = ContinuousLinearMap.id ℝ NormalizedState ∧
        ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
          HasFDerivAt (fun y => normalizedMaxCurve y t₀ t) (J (x, t)) x ∧
          HasDerivAt (fun u => J (x, u))
            ((normalizedDifferential (normalizedMaxCurve x t₀ t)).comp (J (x, t))) t := by sorry
