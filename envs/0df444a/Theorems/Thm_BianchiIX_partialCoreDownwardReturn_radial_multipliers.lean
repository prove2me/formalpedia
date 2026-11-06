-- Prove2me | Theorems.Thm_BianchiIX_partialCoreDownwardReturn_radial_multipliers
-- name    : BianchiIX.partialCoreDownwardReturn_radial_multipliers
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T00:36:30.686915+00:00
-- url     : https://prove2.me/theorems/31731b21-2374-407e-bc06-cd77ea4b981e
-- title:
--   Radial multiplier estimates including vanishing input walls
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
--   For real $k,z$, define
--   $$\Gamma_k(z)=2\arctan(\sinh z)+\frac{24}{10000k}z,
--   \qquad C_* = \exp\left(2\pi+\frac{48}{10000}\right).$$
--   Division at zero has its total real-field meaning.
--
--   Write $\mathfrak r(y)=r(y_0,y_2)$.
--   For a time function $\tau:\mathbb R^4\to\mathbb R$ put
--   $m_i^\tau(y)=M_i(y,0,0,\tau(y))$.
--   Let $\tau_\downarrow(y)$ be the infimum of positive times in the normalized
--   maximal domain at which $(\Psi_0(y,t))_v=1$ with negative event rate, and set
--   $F_\downarrow(y)=\eta(\Psi_0(y,\tau_\downarrow(y)))$.
--   The incoming condition means $y_v>1$, or $y_v=1$ and $y_m\geq1$.
--   Define
--   $$Q_k(u,p;v,dz)=|v_0|+k|v_1|+|v_2|+(k^2u+p/k)|dz|.$$
--   All vector norms are supremum norms and operator norms are induced by them.
--   Let $Y:\mathbb R\to\mathbb R^4$ be
--   differentiable at $x$, $0<r\leq1$, $K\geq1$. Write
--   $k(a)=\mathfrak r(Y(a))$, $U(a)=Y(a)_1$, $P(a)=Y(a)_2Y(a)_3$, $z(a)=\theta(Y(a))$.
--   At $x$ assume $k\geq6$, $Y\in\mathcal K_k$, the incoming condition,
--   $1/k\leq Kr$, $k\leq K/r$, and
--   $$|k'|\leq K/r^2,\quad |U'|\leq KU/r,\quad |P'|\leq KP/r,\quad |z'|\leq K/r.$$
--   Put $m_i(a)=m_i^{\tau_\downarrow}(Y(a))$,
--   $f_U(a)=\Psi_0(Y(a),\tau_\downarrow(Y(a)))_1$ and
--   $f_P(a)=\Psi_0(Y(a),\tau_\downarrow(Y(a)))_3$.
--   Both $m_i$ and $\log m_i$ are differentiable at $x$, $m_i(x)>0$,
--   and $f_U=Um_0$, $f_P=Pm_1$ as germs there. With
--   $A=(200C_*+2)K^2$, $B=1180C_*K^4+4K^2$, $L=\log(4k(x))$,
--   $$| (\log m_0)'(x)|\leq AL/r^2,\quad |(\log m_1)'(x)|\leq BL.$$
--   The two returned walls are nonnegative and differentiable at $x$, and
--   $$|f_U'|\leq f_U(K/r+AL/r^2),\qquad |f_P'|\leq f_P(K/r+BL).$$
--   If $U(x)=0$, then $f_U(x)=f_U'(x)=0$; if $P(x)=0$, then
--   $f_P(x)=f_P'(x)=0$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/PartialCoreDownwardRadialMultipliers.lean#L12-L76

import Definitions.Def_BianchiIX_Analysis_CoreGrowthBudget
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_EraReturnData
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
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Module
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

theorem BianchiIX.partialCoreDownwardReturn_radial_multipliers {Y : ℝ → ProjectiveState} {x r K : ℝ}
    (hr : 0 < r ∧ r ≤ 1) (hK : 1 ≤ K) (hY : DifferentiableAt ℝ Y x) :
    let τ := partialCoreDownwardReturnTime
    let k := fun a => coreRadius (Y a 0) (Y a 2)
    let U := fun a => Y a 1
    let p := fun a => Y a 2 * Y a 3
    let z := fun a => projectiveCoreAngle (Y a)
    let m := fun i a => partialCoreReturnMultiplier τ (Y a) i
    let fU := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a)) 1
    let fP := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a)) 3
    let A := (200 * coreVariationBound + 2) * K ^ 2
    let B := 1180 * coreVariationBound * K ^ 4 + 4 * K ^ 2
    let L := Real.log (4 * k x)
    6 ≤ k x → coreRegion (k x) (Y x) → (1 < Y x 2 ∨ (Y x 2 = 1 ∧ 1 ≤ Y x 0)) →
    1 / k x ≤ K * r → k x ≤ K / r → |deriv k x| ≤ K / r ^ 2 →
    |deriv U x| ≤ K * U x / r → |deriv p x| ≤ K * p x / r → |deriv z x| ≤ K / r →
    (∀ i : Fin 2, 0 < m i x ∧ DifferentiableAt ℝ (m i) x ∧
      DifferentiableAt ℝ (fun a => Real.log (m i a)) x) ∧
    (fU =ᶠ[𝓝 x] fun a => U a * m 0 a) ∧ (fP =ᶠ[𝓝 x] fun a => p a * m 1 a) ∧
    |deriv (fun a => Real.log (m 0 a)) x| ≤ A * L / r ^ 2 ∧
    |deriv (fun a => Real.log (m 1 a)) x| ≤ B * L ∧
    DifferentiableAt ℝ fU x ∧ DifferentiableAt ℝ fP x ∧ 0 ≤ fU x ∧ 0 ≤ fP x ∧
    |deriv fU x| ≤ fU x * (K / r + A * L / r ^ 2) ∧
    |deriv fP x| ≤ fP x * (K / r + B * L) ∧
    (U x = 0 → fU x = 0 ∧ deriv fU x = 0) ∧
    (p x = 0 → fP x = 0 ∧ deriv fP x = 0) := by sorry
