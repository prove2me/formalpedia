-- Prove2me | Theorems.Thm_BianchiIX_normalizedMaxDomain_forward_of_bounds
-- name    : BianchiIX.normalizedMaxDomain_forward_of_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T16:01:28.60352+00:00
-- url     : https://prove2.me/theorems/277d042e-4409-4820-a99d-006322366061
-- title:
--   Finite-time bounds imply forward completeness
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
--   Suppose that for every $T\in\mathbb R$ there exists $R\geq0$ such that
--   $\|\alpha_{x_0,t_0}(t)\|\leq R$ whenever
--   $t\in I_{\max}(x_0,t_0)\cap[t_0,T]$. Then
--   $[t_0,\infty)\subset I_{\max}(x_0,t_0)$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/ForwardComplete.lean#L16-L42

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
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
open scoped Topology

theorem BianchiIX.normalizedMaxDomain_forward_of_bounds {x₀ : NormalizedState} {t₀ : ℝ}
    (hbound : ∀ T : ℝ, ∃ R ≥ (0 : ℝ), ∀ t ∈ normalizedMaxDomain x₀ t₀,
      t ∈ Icc t₀ T → ‖normalizedMaxCurve x₀ t₀ t‖ ≤ R) :
    Ici t₀ ⊆ normalizedMaxDomain x₀ t₀ := by sorry
