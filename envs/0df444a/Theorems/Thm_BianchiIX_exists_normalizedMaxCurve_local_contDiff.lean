-- Prove2me | Theorems.Thm_BianchiIX_exists_normalizedMaxCurve_local_contDiff
-- name    : BianchiIX.exists_normalizedMaxCurve_local_contDiff
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T22:23:14.139143+00:00
-- url     : https://prove2.me/theorems/59a9f5d8-a77d-4d31-a64a-e23d462005a7
-- title:
--   Joint local continuous differentiability in initial state and time
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
--   For every $(x_0,t_0)$ there are
--   $r,\varepsilon>0$ such that, for $I=(t_0-\varepsilon,t_0+\varepsilon)$,
--   $$I\subset I_{\max}(x,t_0)\quad(x\in B(x_0,r)),$$
--   and $(x,t)\mapsto\alpha_{x,t_0}(t)$ is of class $C^1$ on
--   $B(x_0,r)\times I$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/SmoothLocalFlow.lean#L11-L42

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
import Mathlib.Analysis.Calculus.FDeriv.Partial

noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

theorem BianchiIX.exists_normalizedMaxCurve_local_contDiff (x₀ : NormalizedState) (t₀ : ℝ) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ),
      (∀ x ∈ ball x₀ r, Ioo (t₀ - ε) (t₀ + ε) ⊆ normalizedMaxDomain x t₀) ∧
      ContDiffOn ℝ 1 (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2)
        (ball x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)) := by sorry
