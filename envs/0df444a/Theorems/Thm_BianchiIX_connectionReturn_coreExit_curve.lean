-- Prove2me | Theorems.Thm_BianchiIX_connectionReturn_coreExit_curve
-- name    : BianchiIX.connectionReturn_coreExit_curve
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T10:52:19.806198+00:00
-- url     : https://prove2.me/theorems/d921944c-087b-4fd3-ad4f-acca472f2352
-- title:
--   A decreasing core-exit curve retains its physical cone after the connection
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
--   For the positive reflected phase variable $m$, put
--   $$n(a,b)=\sqrt{a^2+b^2},\quad j(a,b)=\frac1{n(a,b)(n(a,b)+a)},$$
--   $$\phi=n(m+1,v)+n(m-1,w)-m,\quad
--   h=\frac{m+1}{n(m+1,v)}+\frac{m-1}{n(m-1,w)}-1,$$
--   $$Q=mh+\frac{v^2}{n(m+1,v)}+\frac{w^2}{n(m-1,w)},\quad
--   k=j(m+1,v)-j(m-1,w).$$
--   Write $\kappa=u(v+w-u)$, $s=m-1-\kappa$,
--   $b=(1-m^2-(v-w)^2+u^2)/2$, and
--   $$M_v=-\frac{v^2}{n(m+1,v)h},\qquad M_w=-\frac{w^2}{n(m-1,w)h}.$$
--   The four coordinate differential operators, in the order
--   $(\phi,\log u,\log v,\log w)$, are
--   $$L_0=h^{-1}\partial_m,\quad L_1=u\partial_u,\quad
--   L_2=M_v\partial_m+v\partial_v,\quad L_3=M_w\partial_m+w\partial_w.$$
--   Subscripts $i$ below denote the rational expressions obtained by these
--   rules, with total real-field division. On the regular positive-wall
--   region they are the corresponding coordinate partial derivatives. Set
--   $$N=h(v-w)+(v+w-u)Q,\quad R=h(v-w)+(v+w-u)(Q-s),$$
--   $$A=-N/s,\quad B=k/s,\quad G=uA+(vw)^2B,\quad
--   \alpha=b/s,\quad \beta=-1-2(1+\kappa)/s.$$
--   The coefficient matrix $C$ has rows $(G_i)_i$, $(\alpha_i)_i$ and
--   $(\beta_i)_i$.
--
--   For a projective state $y$, evaluate the reflected formulas at
--   $(m,u,v,w)=(-y_0,y_1,y_2,y_3)$. Define
--   $$\chi(y)=(\phi,\log y_1,\log y_2,\log y_3),$$
--   $$\mathcal T_y\xi=\left(-h\xi_0+
--   \frac{y_2\xi_2}{n(-y_0+1,y_2)}+
--   \frac{y_3\xi_3}{n(-y_0-1,y_3)},
--   \frac{\xi_1}{y_1},\frac{\xi_2}{y_2},\frac{\xi_3}{y_3}\right).$$
--   Let $\mathcal A_y d=(\sum_i C_{0i}d_i,\sum_i C_{1i}d_i,
--   \sum_i C_{2i}d_i,0)$ and $W_\mu d=(d_1,\mu^2d_2)$, with the sup norm.
--   The original-time clock rate is $\Omega(y)=6\omega_-(y)/D(y)$.
--   For $Y=\Psi_{t_0}(y,t)$ and $\xi=d_y\Psi_{t_0}(y,t)v$, set
--   $$\mathcal P_{y,t_0,t}v=\xi-(\xi_3/Y_3-v_3/y_3)H(Y),\qquad
--   \mathcal D_{y,t_0,t}v=\mathcal T_Y(\mathcal P_{y,t_0,t}v).$$
--   Thus $\mathcal D$ is the logarithmic variation at fixed relative
--   growing-wall clock.
--
--   For entry amplitudes $u,p$, define the feedback budget
--   $$\Lambda_\mu(u,p)=64\left(\frac{2u}{\mu^3}+\frac{p^2}{4\mu^3}\right)
--   +8192\left(\frac{4u}{\mu^2}+\frac{p^2}{16\mu^3}\right).$$
--
--   Write $p=(\mu,u,w)$, $L=-\log w$, and define the physical return and phase error by
--   $$P^{\rm phys}(p)=(n(-P_-(p)_0-1,1),P_-(p)_1,P_-(p)_2),$$
--   $$E(p)=n(-P_-(p)_0-1,1)-n(\mu+1,1)+2.$$
--   Let $f,u,w$ be differentiable at $x$,
--   $f(x)>1$, $f'(x)<0$, and put
--   $p(a)=(\sqrt{f(a)^2-1}-1,u(a),w(a))$, $G(a)=P^{\rm phys}(p(a))$.
--   Suppose $0<\varepsilon\leq1/10000$, $\sqrt\varepsilon\leq10^{-6}$,
--   $\varepsilon\leq e^{-256}$, $p_0(x)\geq4$,
--   $0<u(x)\leq\varepsilon/p_0(x)$, $0<w(x)\leq\varepsilon$,
--   $$|u'(x)|\leq\sqrt{u(x)}|f'(x)|,\qquad
--   |w'(x)|\leq\sqrt{w(x)}|f'(x)|.$$
--   Then $G$ is differentiable at $x$, $G_0'(x)<0$,
--   $$\left|\frac{G_0'(x)}{f'(x)}-1\right|\leq\frac1{4p_0(x)},\qquad
--   \frac34\leq\frac{G_0'(x)}{f'(x)}\leq\frac54,$$
--   $$|G_1'(x)|\leq\sqrt{G_1(x)}|G_0'(x)|,\qquad
--   |G_2'(x)|\leq\sqrt{G_2(x)}|G_0'(x)|.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/ConnectionRadialCurve.lean#L10-L106

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ConnectionEvents
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturn
import Definitions.Def_BianchiIX_Dynamics_ConnectionPhysicalReturn
import Definitions.Def_BianchiIX_Dynamics_CoreConnectionChart
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
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open BianchiIX

theorem BianchiIX.connectionReturn_coreExit_curve {f u w : ℝ → ℝ} {x ε : ℝ}
    (hf : DifferentiableAt ℝ f x) (hu : DifferentiableAt ℝ u x)
    (hw : DifferentiableAt ℝ w x) (hf1 : 1 < f x) (hdf : deriv f x < 0)
    (hε : 0 < ε ∧ ε ≤ 1 / 10000) (hsε : Real.sqrt ε ≤ 1 / 1000000)
    (hεL : ε ≤ Real.exp (-256))
    (hμ : 4 ≤ coreExitConnectionParameters ![f x, u x, w x] 0)
    (hu0 : 0 < u x ∧ u x ≤ ε / coreExitConnectionParameters ![f x, u x, w x] 0)
    (hw0 : 0 < w x ∧ w x ≤ ε)
    (hdu : |deriv u x| ≤ Real.sqrt (u x) * |deriv f x|)
    (hdw : |deriv w x| ≤ Real.sqrt (w x) * |deriv f x|) :
    let p := fun a => coreExitConnectionParameters ![f a, u a, w a]
    let G := fun a => connectionReturnPhysicalState (p a)
    DifferentiableAt ℝ G x ∧
      deriv (fun a => G a 0) x < 0 ∧
      |deriv (fun a => G a 0) x / deriv f x - 1| ≤ 1 / (4 * p x 0) ∧
      (3 / 4 ≤ deriv (fun a => G a 0) x / deriv f x ∧
        deriv (fun a => G a 0) x / deriv f x ≤ 5 / 4) ∧
      |deriv (fun a => G a 1) x| ≤ Real.sqrt (G x 1) * |deriv (fun a => G a 0) x| ∧
      |deriv (fun a => G a 2) x| ≤ Real.sqrt (G x 2) * |deriv (fun a => G a 0) x| := by sorry
