-- Prove2me | Theorems.Thm_BianchiIX_exists_activeWall_first_upward_hit_two
-- name    : BianchiIX.exists_activeWall_first_upward_hit_two
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T08:00:11.859673+00:00
-- url     : https://prove2.me/theorems/ab78de0f-0c17-4a03-9ff1-67d693d3db44
-- title:
--   A positive active-wall flight has a twice differentiable first-hit branch
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
--   Let $g(x)=(\Pi(x))_v$ and put
--   $$\rho(x,t_0,t)=dg_{\alpha_{x,t_0}(t)}N(\alpha_{x,t_0}(t)),\qquad
--   A(x,t_0,t)=1+(\alpha_{x,t_0}(t))_0.$$
--
--   For an observable $g$, put $q=\alpha_{x,t_0}(T)$ and define
--   $$\ell_{g,x,t_0,T}(h)=-\frac{dg_q(J_{x,t_0}(T)h)}{dg_qN(q)},
--   \qquad E_{g,x,t_0,T}(h)=J_{x,t_0}(T)h+\ell_{g,x,t_0,T}(h)N(q).$$
--   Suppose $T>0$,
--   $[0,T]\subset I_{\max}(x,0)$, $A(x,0,t)>0$ and $\rho(x,0,t)>0$
--   throughout $[0,T]$, and $g(\alpha_{x,0}(T))=\eta$.
--   There exists $\tau$ with $\tau(x)=T$ such that $\tau$ and
--   $Q(y)=\Pi(\alpha_{y,0}(\tau(y)))$ are $C^2$ at $x$, with
--   $$d\tau_x=\ell_{g,x,0,T},\qquad
--   dQ_x=d\Pi_{\alpha_{x,0}(T)}\circ E_{g,x,0,T}.$$
--   For all $y$ sufficiently near $x$, $\tau(y)$ is the least positive
--   maximal-domain hit of height $\eta$. The whole interval $[0,\tau(y)]$
--   lies in that domain with positive $A$ and event rate, and its height
--   is below $\eta$ at every earlier time.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/ActiveWallUpwardHit.lean#L57-L104

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_Events
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
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

theorem BianchiIX.exists_activeWall_first_upward_hit_two {x : NormalizedState} {T η : ℝ} (hT : 0 < T)
    (hreg : ∀ t ∈ Icc 0 T, t ∈ normalizedMaxDomain x 0 ∧ 0 < 1 + normalizedMaxCurve x 0 t 0)
    (hrate : ∀ t ∈ Icc 0 T, 0 < normalizedEventRate projectiveActiveWall x 0 t)
    (hhit : projectiveActiveWall (normalizedMaxCurve x 0 T) = η) :
    ∃ τ : NormalizedState → ℝ, τ x = T ∧ ContDiffAt ℝ 2 τ x ∧
      ContDiffAt ℝ 2 (fun y => toProjectiveState (normalizedMaxCurve y 0 (τ y))) x ∧
      HasFDerivAt τ (normalizedEventTimeDifferential projectiveActiveWall x 0 T) x ∧
      HasFDerivAt (fun y => toProjectiveState (normalizedMaxCurve y 0 (τ y)))
        ((fderiv ℝ toProjectiveState (normalizedMaxCurve x 0 T)).comp
          (normalizedEventDifferential projectiveActiveWall x 0 T)) x ∧
      (∀ᶠ y in 𝓝 x,
        IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain y 0 ∧ projectiveActiveWall (normalizedMaxCurve y 0 t) = η} (τ y) ∧
        (∀ t ∈ Icc 0 (τ y), t ∈ normalizedMaxDomain y 0 ∧ 0 < 1 + normalizedMaxCurve y 0 t 0) ∧
        (∀ t ∈ Ico 0 (τ y), projectiveActiveWall (normalizedMaxCurve y 0 t) < η) ∧
        (∀ t ∈ Icc 0 (τ y), 0 < normalizedEventRate projectiveActiveWall y 0 t)) := by sorry
