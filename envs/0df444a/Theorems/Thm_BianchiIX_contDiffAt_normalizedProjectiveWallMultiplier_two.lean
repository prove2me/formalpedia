-- Prove2me | Theorems.Thm_BianchiIX_contDiffAt_normalizedProjectiveWallMultiplier_two
-- name    : BianchiIX.contDiffAt_normalizedProjectiveWallMultiplier_two
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T04:35:18.328231+00:00
-- url     : https://prove2.me/theorems/81c15816-c79f-4f5a-8fc9-588c91c664b0
-- title:
--   Parameterized finite flights have twice differentiable wall factors and logarithms
-- statement:
--   For real variables $p,s,a,b,c$, set
--   $$K=a^2+b^2+c^2-2(ab+bc+ca),\qquad S=p^2+s^2,\qquad C=S+K.$$
--   The shear components and wall rates are
--   $$P=Kp-2a^2+b^2+c^2+ab-2bc+ac,$$
--   $$Q=Ks+\sqrt{3}(-b^2+c^2+ab-ac),$$
--   $$r_1=-S+2p,\qquad r_2=-S-p+\sqrt{3}s,\qquad r_3=-S-p-\sqrt{3}s.$$
--   These functions define the normalized vacuum Bianchi IX vector field
--   $(P,Q,r_1a,r_2b,r_3c)$.
--   For $y=(m,u,v,w)\in\mathbb R^4$, define
--   $$K(u,v,w)=u^2+v^2+w^2-2(uv+vw+wu),\qquad \kappa=u(v+w-u),$$
--   $$F_m=-v^2+w^2+u(v-w)-m\kappa,\qquad
--   F_u=\tfrac12(1-m^2-(v-w)^2+u^2)u,$$
--   $$F_v=(m-1-\kappa)v,\qquad F_w=(-m-1-\kappa)w,\qquad
--   F=(F_m,F_u,F_v,F_w),$$
--   and $E(m,v)=(m-1)^2+v^2$.
--
--   For $x=(p,s,a,b,c)$, put
--   $$\psi(p,z)=\frac{\sqrt3\,z}{1+p},\qquad
--   \Pi(x)=(\psi(p,s),\psi(p,a),\psi(p,b),\psi(p,c)).$$
--   For $y=(m,u,v,w)$, set $D(y)=3+m^2+K(u,v,w)$ and
--   $$\Xi_A(y)=\left(A-1,\frac{Am}{\sqrt3},\frac{Au}{\sqrt3},
--   \frac{Av}{\sqrt3},\frac{Aw}{\sqrt3}\right),\qquad
--   \Xi(y)=\Xi_{6/D(y)}(y).$$
--   Write $N(x)=(P,Q,r_1a,r_2b,r_3c)$ for the normalized vector field
--   and $\mathcal C(x)=C(p,s,a,b,c)$ for its constraint.
--
--   The normalized and projective state spaces are $\mathbb R^5$ and $\mathbb R^4$
--   with their finite-product norms. The maps $\Pi,\Xi,D,F$ act on these state spaces.
--
--   The projective vector field in normalized time is
--   $$G(y)=\frac6{D(y)}F(y).$$
--
--   Write $X=\mathbb R^5$, $Y=\mathbb R^4$, and let $\alpha_{x,t_0}$ be the
--   maximal solution of $\alpha'=N(\alpha)$ with initial value $x$ at $t_0$
--   and domain $I_{\max}(x,t_0)$. Put
--   $$J_{x,t_0}(t)=d_x\alpha_{x,t_0}(t),\qquad
--   \Psi_{t_0}(y,t)=\Pi(\alpha_{\Xi(y),t_0}(t)),$$
--   $$\mathcal J_{y,t_0}(t)=d\Pi_{\alpha_{\Xi(y),t_0}(t)}
--   \circ J_{\Xi(y),t_0}(t)\circ d\Xi_y.$$
--
--   For $x\in\mathbb R^5$, $T\in\mathbb R$, and $i=0,1,2$, define
--   $$M_i(x,T)=\exp\left(\log(1+x_0)
--   -\log(1+(\alpha_{x,0}(T))_0)
--   +\int_0^T r_{i+1}(\alpha_{x,0}(t))\,dt\right).$$
--   The rates $r_1,r_2,r_3$ are the normalized wall rates defined above.
--   Let $E$ be a real normed
--   space, $c:E\to\mathbb R^5$, $\tau:E\to\mathbb R$, and $Y\in E$.
--   Assume $c,\tau$ are $C^2$ at $Y$, $\tau(Y)\geq0$,
--   $$[0,\tau(Y)]\subset I_{\max}(c(Y),0),\qquad
--   1+c(Y)_0>0,\qquad1+(\alpha_{c(Y),0}(\tau(Y)))_0>0.$$
--   For each $i=0,1,2$, the functions
--   $$Z\mapsto M_i(c(Z),\tau(Z)),\qquad
--   Z\mapsto\log M_i(c(Z),\tau(Z))$$
--   are $C^2$ at $Y$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/ProjectiveWallMultipliers.lean#L37-L63

import Definitions.Def_BianchiIX_Dynamics_ProjectiveWallMultipliers
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
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
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed

noncomputable section
open BianchiIX
open Set MeasureTheory

theorem BianchiIX.contDiffAt_normalizedProjectiveWallMultiplier_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : E → NormalizedState} {τ : E → ℝ} {Y : E}
    (hc : ContDiffAt ℝ 2 c Y) (hτ : ContDiffAt ℝ 2 τ Y) (hpos : 0 ≤ τ Y)
    (hdom : Icc 0 (τ Y) ⊆ normalizedMaxDomain (c Y) 0)
    (hA0 : 0 < 1 + c Y 0) (hAT : 0 < 1 + normalizedMaxCurve (c Y) 0 (τ Y) 0) (i : Fin 3) :
    ContDiffAt ℝ 2 (fun Z => normalizedProjectiveWallMultiplier (c Z) (τ Z) i) Y ∧
      ContDiffAt ℝ 2 (fun Z => Real.log (normalizedProjectiveWallMultiplier (c Z) (τ Z) i)) Y := by sorry
