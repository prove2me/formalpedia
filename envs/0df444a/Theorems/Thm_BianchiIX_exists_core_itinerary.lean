-- Prove2me | Theorems.Thm_BianchiIX_exists_core_itinerary
-- name    : BianchiIX.exists_core_itinerary
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T00:37:03.784971+00:00
-- url     : https://prove2.me/theorems/a50f13b3-a9d1-464f-9759-3a1d16eb4a9b
-- title:
--   A prescribed finite core itinerary from a phase margin
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
--   For $Y\in\mathbb R^3$, put $x_Y=\Xi(e(Y))$,
--   $\beta_Y(t)=\Psi_0(e(Y),t)$, and
--   $$H_Y=\{t>0:t\in I_{\max}(x_Y,0),\ (\beta_Y(t))_v=1\},
--   \qquad T(Y)=\inf H_Y,\qquad F(Y)=\eta(\beta_Y(T(Y))).$$
--   The infimum uses the total real-order convention. Write $\operatorname{Valid}(Y)$
--   when $T(Y)$ is the least element of $H_Y$, every $t\in[0,T(Y)]$ lies in
--   $I_{\max}(x_Y,0)$ with $A_{e(Y),0}(t)>0$, the active wall is strictly
--   above one for $0<t<T(Y)$, and
--   $$dg_{\alpha_{x_Y,0}(T(Y))}N(\alpha_{x_Y,0}(T(Y)))<0,
--   \qquad g(x)=(\Pi(x))_v.$$
--   All vector and operator norms below use the finite-product supremum norm.
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
--   Put $c=u(v+w-u)$, $s(m,u,v,w)=m-1-c$,
--   $b(m,u,v,w)=(1-m^2-(v-w)^2+u^2)/2$,
--   $D(m,u,v,w)=3+m^2+K(u,v,w)$, and $r(m,v)=\sqrt{(m-1)^2+v^2}$.
--
--   Define
--   $$\mathcal C_\mu=\{(m,u,v,w):|-m-\mu|\leq1/2,
--   \ 0\leq u\leq1/10000,\ 0\leq v,w\leq1\},$$
--   $$\omega_-(y)=s(-y_m,y_u,y_v,y_w),\qquad H(y)=F(y)/\omega_-(y).$$
--   For a normalized trajectory write
--   $$\beta(t)=\Pi(\alpha_{x,t_0}(t)),\quad A(t)=1+(\alpha_{x,t_0}(t))_0,
--   \quad I=I_{\max}(x,t_0).$$
--
--   For $p=(\mu,u,w)\in\mathbb R^3$, set $e(p)=(-\mu,u,1,w)$,
--   $x_p=\Xi(e(p))$, and
--   $$T_-(p)=\inf\{t>0:t\in I_{\max}(x_p,0),\ (\Psi_0(e(p),t))_w=1\},
--   \qquad P_-(p)=\Psi_0(e(p),T_-(p)).$$
--   Let $V_-(p)$ mean that this infimum is a least element, the full interval
--   $[0,T_-(p)]$ lies in the maximal domain with positive $A$, the growing wall
--   is below one before the endpoint, and its normalized-time derivative is
--   strictly positive at the endpoint. The infimum has its total real-order meaning.
--
--   Write $e_+(R,u,w)=(1+\sqrt{R^2-1},u,1,w)$,
--   $e_-(R,u,w)=(1-\sqrt{R^2-1},u,1,w)$,
--   $p_-(R,u,w)=(\sqrt{R^2-1}-1,u,w)$, and
--   $\mathcal R(m,u,v,w)=(-m,u,w,v)$.
--   The physical connection coordinates are
--   $$\mathscr C(p)=\left(\sqrt{(-P_-(p)_0-1)^2+1},P_-(p)_1,P_-(p)_2\right).$$
--   Below $T$ denotes the canonical core return time from $e_+$ and
--   $F(Y)=\eta(\Psi_0(e_+(Y),T(Y)))$ its radial and wall coordinates.
--   Let $\mathscr R(Y)=\mathscr C(p_-(Y))$, $t_r(Y)=T_-(p_-(Y))$,
--   $G=\mathscr R\circ F$, and $t_G(Y)=T(Y)+t_r(F(Y))$.
--   A cone direction at $Y$ has $d_0=1$,
--   $|d_1|\leq\sqrt{Y_1}$, $|d_2|\leq\sqrt{Y_2}$.
--   For a map $H$ with positive output walls, its positive cone property means
--   $dH(Y)d$ has positive radial component and
--   $|(dH(Y)d)_i|\leq\sqrt{H(Y)_i}(dH(Y)d)_0$ for $i=1,2$.
--   There are $0<\varepsilon\leq10^{-4}$
--   and $K>0$ such that the following holds. Let $m\in\mathbb N$,
--   $0<\beta<1/2$, $0<X_1,X_2\leq\varepsilon/X_0$,
--   $m+1+\beta\leq X_0/2\leq m+2-\beta$, and $K(X_1+X_2)<\beta/2$.
--   Put $Y_j=G^j(X)$, $b=X_1+X_2$. For every $j\leq m$,
--   $(Y_j)_0>2+3\beta/2$, its core return is valid,
--   $G^j,F\circ G^j,T\circ G^j$ are $C^1$ at $X$,
--   $F(Y_j)_1,F(Y_j)_2>0$, their sum is at most $b$, and
--   $$|(Y_j)_0-(X_0-2j)|+|F(Y_j)_0-(X_0-2j)|\leq Kb.$$
--   The map $F\circ G^j$ has the positive cone property and radial logarithmic
--   distortion at most $K\sqrt b$. For $j<m$, $F(Y_j)_0>4+3\beta/2$,
--   $t_G(Y_j)>0$, and the reflected flow identity holds.
--   Finally
--   $$2+3\beta/2<F(Y_m)_0<4-3\beta/2,\quad
--   \lfloor X_0/2\rfloor_{\mathbb N}=m+1,$$
--   $$3\beta/4<(F(Y_m)_0-2)/2<1-3\beta/4.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/CoreItinerary.lean#L8-L127

import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_ProjectiveReflection
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreReturnDifferential
import Definitions.Def_BianchiIX_Dynamics_CompactCoreReturn
import Definitions.Def_BianchiIX_EraReturnData
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Algebra.Order.Floor.Ring

noncomputable section
open BianchiIX

theorem BianchiIX.exists_core_itinerary :
    ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∃ K > (0 : ℝ),
      ∀ (m : ℕ) (β : ℝ) (X : CoreAngleState), 0 < β → β < 1 / 2 →
        (0 < X 1 ∧ X 1 ≤ ε / X 0) → (0 < X 2 ∧ X 2 ≤ ε / X 0) →
        ((m : ℝ) + 1 + β ≤ X 0 / 2 ∧ X 0 / 2 ≤ (m : ℝ) + 2 - β) →
        K * (X 1 + X 2) < β / 2 →
        let F := coreReturnState coreRadiusReturnTime
        let G := coreReflectionState coreRadiusReturnTime
        let Y := fun j => G^[j] X
        (∀ j ≤ m,
          2 + 3 * β / 2 < Y j 0 ∧ coreRadiusReturnValid (Y j) ∧
          ContDiffAt ℝ 1 (G^[j]) X ∧ ContDiffAt ℝ 1 (F ∘ G^[j]) X ∧
          ContDiffAt ℝ 1 (coreRadiusReturnTime ∘ G^[j]) X ∧
          (∀ i : Fin 2, 0 < F (Y j) i.succ) ∧ F (Y j) 1 + F (Y j) 2 ≤ X 1 + X 2 ∧
          |Y j 0 - (X 0 - 2 * j)| + |F (Y j) 0 - (X 0 - 2 * j)| ≤ K * (X 1 + X 2) ∧
          ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (X 1) → |v 2| ≤ Real.sqrt (X 2) →
            let d := fderiv ℝ (F ∘ G^[j]) X v
            0 < d 0 ∧ |Real.log (d 0)| ≤ K * Real.sqrt (X 1 + X 2) ∧
              ∀ i : Fin 2, |d i.succ| ≤ Real.sqrt (F (Y j) i.succ) * d 0) ∧
        (∀ j < m, 4 + 3 * β / 2 < F (Y j) 0 ∧ 0 < coreReflectionTime (Y j) ∧
          coreRadiusEntry (Y (j + 1)) = projectiveReflection
            (projectiveOriginalFlow (coreRadiusEntry (Y j)) 0 (coreReflectionTime (Y j)))) ∧
        (2 + 3 * β / 2 < F (Y m) 0 ∧ F (Y m) 0 < 4 - 3 * β / 2) ∧
        Nat.floor (X 0 / 2) = m + 1 ∧
        (3 * β / 4 < (F (Y m) 0 - 2) / 2 ∧ (F (Y m) 0 - 2) / 2 < 1 - 3 * β / 4) := by sorry
