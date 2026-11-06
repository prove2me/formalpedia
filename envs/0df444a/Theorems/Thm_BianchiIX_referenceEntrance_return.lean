-- Prove2me | Theorems.Thm_BianchiIX_referenceEntrance_return
-- name    : BianchiIX.referenceEntrance_return
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T04:06:55.7429+00:00
-- url     : https://prove2.me/theorems/0ea21e28-a5bd-4a8c-9131-121bf45a8a4e
-- title:
--   The first entrance time along an explicit reference pulse
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
--   For real $k,t$, define the boundary pulse
--   $$\beta_k(t)=(m_k(t),0,v_k(t),0)
--   =\left(1-k\tanh(kt),0,\frac{k}{\cosh(kt)},0\right).$$
--
--   Set
--   $$h_k=\frac{\operatorname{arcosh}k}{k},\qquad
--   T_k=\frac{(k^2+4)\operatorname{arcosh}k}{3k},\qquad
--   d_k=\sqrt{k^2-1},$$
--   $$H_k(t)=\frac{k^2+4}{6}t-\frac13\log\cosh(kt).$$
--   Use the total real conventions $x/0=0$, $\sqrt{x}=\sqrt{\max(x,0)}$,
--   $\log0=0$, and $\log x=\log|x|$ for $x<0$, with
--   $\operatorname{arcosh}x=\log(x+\sqrt{x^2-1})$.
--   Write $\alpha_{x,0}$ for the maximal normalized solution starting at $x$
--   at time zero, with domain $I_{\max}(x,0)$.
--
--   Write $X=\mathbb R^5$, $Y=\mathbb R^4$, and let $\alpha_{x,t_0}$ be the
--   maximal solution of $\alpha'=N(\alpha)$ with initial value $x$ at $t_0$
--   and domain $I_{\max}(x,t_0)$. Put
--   $$J_{x,t_0}(t)=d_x\alpha_{x,t_0}(t),\qquad
--   \Psi_{t_0}(y,t)=\Pi(\alpha_{\Xi(y),t_0}(t)),$$
--   $$\mathcal J_{y,t_0}(t)=d\Pi_{\alpha_{\Xi(y),t_0}(t)}
--   \circ J_{\Xi(y),t_0}(t)\circ d\Xi_y.$$
--
--   Define the projective height time and normalized tail duration by
--   $$s_\eta(k)=\frac{\operatorname{arcosh}(k/\eta)}k,\qquad
--   \Delta_\eta(k)=\int_{h_k}^{s_\eta(k)}\frac{D(\beta_k(s))}{6}\,ds.$$
--   Write $x_k^+=\Xi(\beta_k(h_k))$, $g(x)=(\Pi(x))_v$, and
--   $\rho(x,t)=dg_{\alpha_{x,0}(t)}N(\alpha_{x,0}(t))$.
--
--   Let $k\ge7/4$, $0<v<1$, $e=(1+\sqrt{k^2-v^2},0,v,0)$ and
--   $s_v=\operatorname{arcosh}(k/v)/k$, $h_k=\operatorname{arcosh}(k)/k$.
--   For the reference clock primitive $H_k$, the first unit entrance time
--   from $e$ is $H_k(-h_k)-H_k(-s_v)$ and its state is the reference pulse
--   at $-h_k$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/ReferenceEntrance.lean#L53-L102

import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ReferencePulse
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ReferenceReturn
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_ReferenceTail
import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Definitions.Def_BianchiIX_Dynamics_EntranceReturn
import Definitions.Def_BianchiIX_GeometricExceptionData
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Pow
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
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed

noncomputable section
open BianchiIX
open Set

theorem BianchiIX.referenceEntrance_return {k v : ℝ} (hk : 7 / 4 ≤ k) (hv : 0 < v ∧ v < 1) :
    entranceReturnTime (referenceEntranceState k v) =
        referenceShiftClock k (-referenceHeightTime k v) (-referenceHalfTime k) ∧
      entranceReturnState (referenceEntranceState k v) = referencePulse k (-referenceHalfTime k) := by sorry
