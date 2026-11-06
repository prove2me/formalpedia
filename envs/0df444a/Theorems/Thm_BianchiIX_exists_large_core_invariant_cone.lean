-- Prove2me | Theorems.Thm_BianchiIX_exists_large_core_invariant_cone
-- name    : BianchiIX.exists_large_core_invariant_cone
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T03:34:11.300134+00:00
-- url     : https://prove2.me/theorems/861b5ab6-9cd9-4cce-873b-21de0f49a08f
-- title:
--   The actual large-core first return strictly preserves the square-root tangent cone
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
--   At $(z,Y)$ use the abbreviations
--   $$s=1/\cosh z,\quad c=-\tanh z,\quad \delta=u-w,$$
--   $$C=u(v+w-u),\quad a=-r/2+\tanh z+w/\cosh z+(u^2-w^2)/(2r),
--   \quad g=-C+c\delta^2/r.$$
--   Let $\mathcal Q(z,Y)=(C,d,a,g)$. Define the $4\times3$ matrix $H(z,Y)$
--   by its rows, in the order $(C,d,a,g)$ and columns $(r,u,p)$:
--   $$H_C=(u(s-w/r),\ v-2u+w,\ u/v),$$
--   $$H_d=(2\delta(u-2w)/r^3,\ -2\delta/r^2,\ 2\delta/(vr^2)),$$
--   $$H_a=(-1/2-sw/r+(3w^2-u^2)/(2r^2),\ u/r,\ (1-w/v)/r),$$
--   $$H_g=(-u(s-w/r)+c\delta(3w-u)/r^2,\
--   -(v-2u+w)+2c\delta/r,\ -u/v-2c\delta/(rv)).$$
--
--   Define the two rates and the $2\times3$ matrix $J$ by
--   $$L_0(z,Y)=a/d,\qquad L_1(z,Y)=-2(1+C)/(rd),$$
--   $$J_{0j}=H_{aj}/d-aH_{dj}/d^2,$$
--   $$J_{1j}=\delta_{j0}\frac{2(1+C)}{r^2d}
--   -\frac{2H_{Cj}}{rd}+\frac{2(1+C)H_{dj}}{rd^2},\qquad j=0,1,2.$$
--   Here $\delta_{j0}$ is the Kronecker symbol. The total formulas are defined
--   also when a wall amplitude vanishes, and use $x/0=0$.
--
--   Define the rates in normalized time and the positive flow factors by
--   $$R(y)=\lambda(y)L(\theta_y,\eta(y)),\qquad
--   M_i(y,t_0,a,b)=\exp\left(\int_a^b R_i(\Psi_{t_0}(y,t))\,dt\right),
--   \quad i=0,1.$$
--   The interval integral is oriented and uses its total Bochner-integral
--   definition for every choice of endpoints and initial data.
--
--   For $\tau:\mathbb R^3\to\mathbb R$, define
--   $$A_i^\tau(Z)=M_i(e(Z),0,0,\tau(Z)),\qquad
--   \mathscr R_i^\tau(Z,s)=\tau(Z)R_i(\Psi_0(e(Z),s\tau(Z))).$$
--   Put
--   $F_\tau(Z)=\eta(\Psi_0(e(Z),\tau(Z)))$. There is
--   $0<\varepsilon\leq1/10000$ such that, whenever $Y=(k,u,w)$,
--   $k\geq6$, and $0\leq u,w\leq\varepsilon/k$, there is a time function
--   $\tau$ with $\tau(Y)>0$ and both $\tau,F_\tau$ of class $C^1$ at $Y$.
--   For $Z$ near $Y$, $\tau(Z)$ is the least positive active-wall return,
--   and the returned walls are $Z_1A_0^\tau(Z)$ and $Z_2A_1^\tau(Z)$.
--   For every $v$ with $v_0=1$, $|v_1|\leq\sqrt u$, and
--   $|v_2|\leq\sqrt w$, put $W=dF_\tau|_Yv$. Then
--   $$W_0>0,\qquad |W_0-1|\leq\frac1{32k},$$
--   $$|W_i|\leq\left(1-\frac1{16k}\right)
--   \sqrt{F_\tau(Y)_i}\,W_0\qquad(i=1,2).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/CoreConeInvariance.lean#L11-L67

import Definitions.Def_BianchiIX_Analysis_CoreGrowthBudget
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreMultipliers
import Definitions.Def_BianchiIX_Dynamics_CoreMultiplierDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreReturnDifferential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

theorem BianchiIX.exists_large_core_invariant_cone :
    ∃ ε > 0, ε ≤ 1 / 10000 ∧ ∀ Y : CoreAngleState, 6 ≤ Y 0 →
      (0 ≤ Y 1 ∧ Y 1 ≤ ε / Y 0) → (0 ≤ Y 2 ∧ Y 2 ≤ ε / Y 0) →
      ∃ τ : CoreAngleState → ℝ, 0 < τ Y ∧ ContDiffAt ℝ 1 τ Y ∧
        ContDiffAt ℝ 1 (coreReturnState τ) Y ∧
        (∀ᶠ Z in 𝓝 Y,
          IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Z) 0 t 2 = 1} (τ Z) ∧
          projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 1 = Z 1 * coreReturnMultiplier τ Z 0 ∧
          projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 3 = Z 2 * coreReturnMultiplier τ Z 1) ∧
        ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 1) → |v 2| ≤ Real.sqrt (Y 2) →
          let W := fderiv ℝ (coreReturnState τ) Y v
          0 < W 0 ∧ |W 0 - 1| ≤ 1 / (32 * Y 0) ∧
            |W 1| ≤ (1 - 1 / (16 * Y 0)) * Real.sqrt (coreReturnState τ Y 1) * W 0 ∧
            |W 2| ≤ (1 - 1 / (16 * Y 0)) * Real.sqrt (coreReturnState τ Y 2) * W 0 := by sorry
