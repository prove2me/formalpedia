-- Prove2me | Theorems.Thm_BianchiIX_hasDerivAt_coreProjectedFlowVariation
-- name    : BianchiIX.hasDerivAt_coreProjectedFlowVariation
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T23:44:44.022615+00:00
-- url     : https://prove2.me/theorems/7cb139b7-3c3e-44be-9a5d-42ccc59ad9ff
-- title:
--   The actual initial-state differential obeys the projected core equation
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
--   For $j=0,1,2$, define the $3\times3$ matrix $A(z,Y)$ by
--   $$A_{0j}=H_{gj}/d-gH_{dj}/d^2,$$
--   $$A_{1j}=\delta_{j1}a/d+uH_{aj}/d-uaH_{dj}/d^2,$$
--   $$A_{2j}=\delta_{j0}\frac{2p(1+C)}{r^2d}
--   -\delta_{j2}\frac{2(1+C)}{rd}-\frac{2pH_{Cj}}{rd}
--   +\frac{2p(1+C)H_{dj}}{rd^2},$$
--   where $\delta_{ij}$ is the Kronecker symbol.
--
--   Write $X=\mathbb R^5$, $Y=\mathbb R^4$, and let $\alpha_{x,t_0}$ be the
--   maximal solution of $\alpha'=N(\alpha)$ with initial value $x$ at $t_0$
--   and domain $I_{\max}(x,t_0)$. Put
--   $$J_{x,t_0}(t)=d_x\alpha_{x,t_0}(t),\qquad
--   \Psi_{t_0}(y,t)=\Pi(\alpha_{\Xi(y),t_0}(t)),$$
--   $$\mathcal J_{y,t_0}(t)=d\Pi_{\alpha_{\Xi(y),t_0}(t)}
--   \circ J_{\Xi(y),t_0}(t)\circ d\Xi_y.$$
--
--   Set $G(y)=6F(y)/D(y)$ and $\lambda(y)=6r_yd_y/D(y)$. Define
--   $$\mathcal P_y\xi=d\eta_y\xi-d\theta_y\xi\,\mathcal V(\theta_y,\eta(y)),$$
--   $$\mathcal W_{y,t_0,w}(t)=
--   \mathcal P_{\Psi_{t_0}(y,t)}\bigl(\mathcal J_{y,t_0}(t)w\bigr).$$
--   Suppose $D(y)>0$,
--   $t\in I_{\max}(\Xi(y),t_0)$, and
--   $1+(\alpha_{\Xi(y),t_0}(t))_0>0$. Put $q=\Psi_{t_0}(y,t)$ and assume
--   $q_v>0$ and $d_q\ne0$. For every $w\in\mathbb R^4$,
--   $$\mathcal W_{y,t_0,w}'(t)=\lambda(q)A(\theta_q,\eta(q))
--   \mathcal W_{y,t_0,w}(t).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/CoreFlowVariation.lean#L67-L84

import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Definitions.Def_BianchiIX_Dynamics_CoreLinearization
import Definitions.Def_BianchiIX_Dynamics_CoreFlowVariation
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

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

theorem BianchiIX.hasDerivAt_coreProjectedFlowVariation {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hV : 0 < projectiveOriginalFlow y t₀ t 2)
    (hd : coreClockFactor (coreRadius (projectiveOriginalFlow y t₀ t 0)
      (projectiveOriginalFlow y t₀ t 2)) (projectiveOriginalFlow y t₀ t 1)
        (projectiveOriginalFlow y t₀ t 3) ≠ 0) (w : ProjectiveState) :
    HasDerivAt (fun s => coreProjectedFlowVariation y t₀ s w)
      (coreOriginalClockRate (projectiveOriginalFlow y t₀ t) •
        (coreAngleJacobian (projectiveCoreAngle (projectiveOriginalFlow y t₀ t))
          (toCoreAngleState (projectiveOriginalFlow y t₀ t))).mulVec
            (coreProjectedFlowVariation y t₀ t w)) t := by sorry
