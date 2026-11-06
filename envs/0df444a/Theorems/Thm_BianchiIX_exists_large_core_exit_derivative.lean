-- Prove2me | Theorems.Thm_BianchiIX_exists_large_core_exit_derivative
-- name    : BianchiIX.exists_large_core_exit_derivative
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T02:11:47.124899+00:00
-- url     : https://prove2.me/theorems/32c899b3-5ad4-43bd-b795-565ed34368a0
-- title:
--   Every admissible core entrance has an actual moving-exit derivative
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
--   Define the core radius, angle, and clock factor by
--   $$r(m,v)=\sqrt{(m-1)^2+v^2},\qquad
--   \theta(m,v)=\operatorname{arsinh}\frac{1-m}{v},\qquad
--   d(r,u,w)=1-\frac{(u-w)^2}{r^2}.$$
--   For $y=(m,u,v,w)$, write $r_y=r(m,v)$, $\theta_y=\theta(m,v)$,
--   and $d_y=d(r_y,u,w)$. All quotients use the total convention $x/0=0$.
--
--   The core state space is $\mathbb R^3$ with coordinates $Y=(r,u,p)$.
--   Define
--   $$\eta(m,u,v,w)=(r(m,v),u,vw),\qquad
--   \iota_z(r,u,p)=\left(1-r\tanh z,u,\frac r{\cosh z},
--   \frac p{r/\cosh z}\right).$$
--   For fixed $(z,Y)$ put $v=r/\cosh z$, $w=p/v$, $d=d(r,u,w)$, and define
--   $$\mathcal V(z,Y)=\left(
--   \frac{-\kappa(u,v,w)-\tanh z\,(u-w)^2/r}{d},\quad
--   \frac{u[-r/2+\tanh z+w/\cosh z+(u^2-w^2)/(2r)]}{d},\quad
--   \frac{-2p(1+\kappa(u,v,w))}{rd}\right).$$
--
--   For real $k$, put $\varepsilon_k=1/(10000k)$ and define
--   $$\mathcal K_k=\{(m,u,v,w): |E(m,v)-k^2|\leq1/8,\quad v\geq1,
--   \quad0\leq u\leq\varepsilon_k,\quad0\leq vw\leq\varepsilon_k\}.$$
--
--   Write $X=\mathbb R^5$, $Y=\mathbb R^4$, and let $\alpha_{x,t_0}$ be the
--   maximal solution of $\alpha'=N(\alpha)$ with initial value $x$ at $t_0$
--   and domain $I_{\max}(x,t_0)$. Put
--   $$J_{x,t_0}(t)=d_x\alpha_{x,t_0}(t),\qquad
--   \Psi_{t_0}(y,t)=\Pi(\alpha_{\Xi(y),t_0}(t)),$$
--   $$\mathcal J_{y,t_0}(t)=d\Pi_{\alpha_{\Xi(y),t_0}(t)}
--   \circ J_{\Xi(y),t_0}(t)\circ d\Xi_y.$$
--
--   Write $G(y)=6F(y)/D(y)$, $\lambda(y)=6r_yd_y/D(y)$, and
--   $S_k(R,U,P)=(R,kU,P)$. Define
--   $$\mathcal P_y\xi=d\eta_y\xi-d\theta_y\xi\,\mathcal V(\theta_y,\eta(y)),
--   \qquad \mathcal W_{y,t_0,w}(t)=
--   \mathcal P_{\Psi_{t_0}(y,t)}(\mathcal J_{y,t_0}(t)w).$$
--   The entrance parametrization and radial exit factor are
--   $$e(k,u,w)=(1+\sqrt{k^2-1},u,1,w),$$
--   $$f_y=\mathcal V(\theta_y,\eta(y))_0,\qquad c_y=-\tanh\theta_y,
--   \qquad h_y=c_y+f_y/r_y,\qquad \rho_y=c_y/h_y.$$
--   For projective initial data $y$, put
--   $$A_{y,t_0}(t)=1+(\alpha_{\Xi(y),t_0}(t))_0.$$
--   Coordinates of three-vectors are indexed by $0,1,2$; projective
--   coordinates are indexed by $m,u,v,w$.
--
--   For normalized initial data $x$, let $X=\alpha_{x,t_0}(t)$ and
--   $g(X)=(\Pi(X))_v$. Define the event differential by
--   $$\ell_{x,t_0,t}(v)=-[dg_XN(X)]^{-1}dg_XJ_{x,t_0}(t)v,
--   \qquad \mathscr H_{x,t_0,t}(v)=J_{x,t_0}(t)v+\ell_{x,t_0,t}(v)N(X).$$
--   Its expression in projective initial and final coordinates is
--   $$L_{y,t_0,t}=d\Pi_{\alpha_{\Xi(y),t_0}(t)}
--   \circ\mathscr H_{\Xi(y),t_0,t}\circ d\Xi_y.$$
--   For a time function $\tau$, write $M_\tau(z)=\Psi_{t_0}(z,\tau(z))$.
--
--   Let $Y=(k,u_0,w_0)$ satisfy $k\geq6$ and
--   $0\leq u_0,w_0\leq\varepsilon_k$.
--
--   Set $y=e(Y)$ and $t_0=0$. There is a least positive return time $T$
--   to $(\Psi_0(y,T))_v=1$. For $b=\Psi_0(y,T)$,
--   $$0<\rho_b\leq1,\qquad |\rho_b-1|\leq8(u_0/k+w_0^2/k^2).$$
--   There is a function $\tau$, $C^1$ at $y$, with $\tau(y)=T$.
--   For $z$ near $y$, $\tau(z)\in I_{\max}(\Xi(z),0)$,
--   $A_{z,0}(\tau(z))>0$, and $(M_\tau(z))_v=1$. Jointly near $(y,T)$,
--   $$ (\Psi_0(z,s))_v=1\quad\Longleftrightarrow\quad\tau(z)=s.$$
--   The maps $\eta\circ M_\tau$ and $\theta\circ M_\tau$ are $C^1$ at $y$.
--   For every $v\in\mathbb R^4$ put $q=\mathcal W_{y,0,v}(T)_0$. Then
--   $$d(\theta\circ M_\tau)_yv=-q/(r_bh_b),\qquad
--   d(\eta\circ M_\tau)_y(v)_0=\rho_bq,$$
--   $$|d(\eta\circ M_\tau)_y(v)_0|\leq|q|,\qquad
--   |d(\theta\circ M_\tau)_yv|\leq2|q|/k.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/CoreExitEvents.lean#L199-L244

import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveClock
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_Dynamics_CoreExitFactor
import Definitions.Def_BianchiIX_Dynamics_CoreExitEvents
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Module
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

theorem BianchiIX.exists_large_core_exit_derivative {k u w : ℝ} (hk : 6 ≤ k)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k) :
    let y : ProjectiveState := ![1 + Real.sqrt (k ^ 2 - 1), u, 1, w]
    ∃ T > 0, IsLeast {t | 0 < t ∧ projectiveOriginalFlow y 0 t 2 = 1} T ∧
      0 < coreExitRadialFactor (projectiveOriginalFlow y 0 T) ∧
      coreExitRadialFactor (projectiveOriginalFlow y 0 T) ≤ 1 ∧
      |coreExitRadialFactor (projectiveOriginalFlow y 0 T) - 1| ≤ 8 * (u / k + w ^ 2 / k ^ 2) ∧
      ∃ τ : ProjectiveState → ℝ, τ y = T ∧ ContDiffAt ℝ 1 τ y ∧
        (∀ᶠ z in 𝓝 y, τ z ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧
          0 < 1 + normalizedMaxCurve (fromProjectiveState z) 0 (τ z) 0 ∧
          projectiveOriginalFlow z 0 (τ z) 2 = 1) ∧
        (∀ᶠ z : ProjectiveState × ℝ in 𝓝 (y, T),
          projectiveOriginalFlow z.1 0 z.2 2 = 1 ↔ τ z.1 = z.2) ∧
        ContDiffAt ℝ 1 (fun z => toCoreAngleState (projectiveOriginalFlow z 0 (τ z))) y ∧
        ContDiffAt ℝ 1 (fun z => projectiveCoreAngle (projectiveOriginalFlow z 0 (τ z))) y ∧
        ∀ v : ProjectiveState,
          let b := projectiveOriginalFlow y 0 T
          let q := coreProjectedFlowVariation y 0 T v 0
          fderiv ℝ (fun z => projectiveCoreAngle (projectiveOriginalFlow z 0 (τ z))) y v =
            -q / (coreRadius (b 0) (b 2) * (-Real.tanh (projectiveCoreAngle b) +
              coreAngleField (projectiveCoreAngle b) (toCoreAngleState b) 0 / coreRadius (b 0) (b 2))) ∧
          (fderiv ℝ (fun z => toCoreAngleState (projectiveOriginalFlow z 0 (τ z))) y v) 0 =
            coreExitRadialFactor b * q ∧
          |(fderiv ℝ (fun z => toCoreAngleState (projectiveOriginalFlow z 0 (τ z))) y v) 0| ≤ |q| ∧
          |fderiv ℝ (fun z => projectiveCoreAngle (projectiveOriginalFlow z 0 (τ z))) y v| ≤
            2 * |q| / k := by sorry
