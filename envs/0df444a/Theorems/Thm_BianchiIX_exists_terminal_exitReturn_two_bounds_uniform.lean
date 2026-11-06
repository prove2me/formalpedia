-- Prove2me | Theorems.Thm_BianchiIX_exists_terminal_exitReturn_two_bounds_uniform
-- name    : BianchiIX.exists_terminal_exitReturn_two_bounds_uniform
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T19:38:37.477822+00:00
-- url     : https://prove2.me/theorems/69fba193-3329-44ce-b11b-8c040601bdda
-- title:
--   Uniform first and second derivatives of the radial exit return
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
--   For $Y=(k,u,w)\in\mathbb R^3$, define
--   $$e_-(Y)=(1-\sqrt{k^2-1},u,1,w),\quad x_Y=\Xi(e_-(Y)),\quad
--   \beta_Y(t)=\Psi_0(e_-(Y),t),\quad g(x)=(\Pi(x))_v.$$
--   For any real height $\eta$, put
--   $$H_{\eta,Y}=\{t>0:t\in I_{\max}(x_Y,0),\ g(\alpha_{x_Y,0}(t))=\eta\},$$
--   $$T_\eta(Y)=\inf H_{\eta,Y},\qquad P_\eta(Y)=\beta_Y(T_\eta(Y)).$$
--   The infimum uses the total real-order convention. Let
--   $\operatorname{TailValid}_\eta(Y)$ mean that $T_\eta(Y)$ is the least
--   element of $H_{\eta,Y}$, and, writing $T=T_\eta(Y)$, that
--   $$t\in I_{\max}(x_Y,0),\quad 1+(\alpha_{x_Y,0}(t))_0>0
--   \quad(0\leq t\leq T),$$
--   $$g(\alpha_{x_Y,0}(t))>\eta\quad(0\leq t<T),$$
--   $$dg_{\alpha_{x_Y,0}(t)}N(\alpha_{x_Y,0}(t))<0,\quad
--   |(\Pi(\alpha_{x_Y,0}(t)))_w|<1/2\quad(0\leq t\leq T).$$
--   All vector and operator norms use the finite-product supremum norms.
--
--   For $y\in\mathbb R^4$, put $x_y=\Xi(y)$,
--   $$T_+(y)=\inf\{t>0:t\in I_{\max}(x_y,0),\ (\Psi_0(y,t))_v=1\},
--   \qquad P_+(y)=\Psi_0(y,T_+(y)).$$
--   Let $V_+(y)$ mean that this infimum is a least element, the full interval
--   $[0,T_+(y)]$ lies in the maximal domain with
--   $1+(\alpha_{x_y,0}(t))_0>0$, the active wall
--   is below one before the endpoint, and its normalized-time derivative is
--   strictly positive throughout the interval. The infimum has its total
--   real-order meaning.
--
--   For $y=(m,u,v,w)$ define the cyclic chart by
--   $$H(y)=(m+1)^2+K(u,v,w),\qquad
--   \mathcal A(y)=(1-4(m+1)/H,4v/H,4w/H,4u/H).$$
--   Its normalized symmetry is
--   $$A(p,s,a,b,c)=((-p+\sqrt3s)/2,(-\sqrt3p-s)/2,b,c,a).$$
--   Put $z_h(Y)=\mathcal A(P_h(Y))$ and
--   $$\mathcal T(h,Y)=T_h(Y)+T_+(z_h(Y)),\qquad
--   \mathcal P(h,Y)=P_+(z_h(Y)),\qquad x_Y^c=A\Xi(e_-(Y)).$$
--   Write $r(m,v)=\sqrt{(m-1)^2+v^2}$ and $g_*(x)=(\Pi(x))_v$.
--
--   On the invariant plane with zero active wall, use $y=(m,u,w)\in\mathbb R^3$,
--   the inclusion $\iota(m,u,w)=(m,u,0,w)$ and the restriction
--   $\pi_s(m,u,v,w)=(m,u,w)$. Define
--   $$f(y)=\left(mu^2-(m+1)uw+w^2,
--   \frac{1-m^2-w^2+u^2}{2}u,-(m+1+uw-u^2)w\right),$$
--   $$\Delta(y)=3+m^2+(u-w)^2,\qquad f_o(y)=6f(y)/\Delta(y).$$
--   Write $J=df$, $H=d^2f$, $J_o=df_o$, $H_o=d^2f_o$ for their explicit
--   Jacobian and Hessian expressions. The denominator derivatives are
--   $d\Delta=(2m,2(u-w),2(w-u))$ and
--   $d^2\Delta(v,z)=2v_0z_0+2(v_1-v_2)(z_1-z_2)$.
--   The exact original-time boundary flow and its projected variation are
--   $$\Phi(y,t)=\pi_s\Psi_0(\iota y,t),\qquad
--   L(y,t)=\pi_s\mathcal J_{\iota y,0}(t)\iota.$$
--   For a fixed scale $K$, set $\Phi_K(y,s)=\Phi(y,Ks)$,
--   $L_K(y,s)=L(y,Ks)$ and $Q_K(y,s)=d_yL_K(y,s)$.
--   For directions $v,z$, define
--   $$S_K(y,s;v,z)=K\left[H_o(\Phi_K)(L_Kv,L_Kz)+J_o(\Phi_K)Q_K(v,z)\right].$$
--   All vector norms are sup norms, and operator norms are induced by them.
--   Write $b(y)=|u|+|w|$, $E(y)=e^{512b(y)}$, $v_s=(v_1,v_2)$, and
--   $$\mathcal H(y;v,z)=b(y)\|v\|\|z\|+\|v_s\|\|z\|+\|v\|\|z_s\|,$$
--   $$B_2(y)=192b(y)(40000E(y)^3)+10000E(y)^2.$$
--   The closed boundary region is
--   $\mathcal S_c=\{(m,u,0,w):|m-c|\leq1/10,\ |u|,|w|\leq1/100\}$.
--   The boundary projection $P(m,u,w)$ is the limit of $\Phi(m,u,w;t)_0$
--   as $t\to\infty$, using the total limit convention of the formal definitions.
--
--   Set $p(y)=P(y_0,y_1,y_3)$, $\rho(y)=\sqrt{(p(y)-1)^2+y_2^2}$,
--   and $\chi(y)=(\rho(y),y_1,y_2,y_3)$.
--   An admissible inverse $\psi$ at $y$ is $C^2$ at $\chi(y)$,
--   maps $\chi(y)$ to $y$, and is a two-sided local inverse of $\chi$;
--   its derivative is the inverse of the triangular derivative of $\chi$.
--   In the following notation put $y_h=\mathcal A\circ P_h$ and
--   $z_h=\chi\circ y_h$. Define
--   $$F_h(Y)=r(\mathcal P(h,Y)_0,\mathcal P(h,Y)_2),\quad
--   D_h=F_h-(z_h)_0,\quad Q_h=2/F_h-2/(z_h)_0.$$
--   For $I(m,u)=(1+m^2+u^2)/m$ let
--   $$\lambda_+(I)=(I+\sqrt{I^2-4})/2,\qquad
--   s(m,u)=2/(\lambda_+(I(m,u))-1).$$
--   Set $S_h=s((y_h)_0,(y_h)_1)$,
--   $Q_h^s=2/(z_h)_0-S_h$, $E_h=2/F_h-S_h$, and $B_h=2/F_h$.
--   The positive wall multipliers $m_0,m_1$ are defined by integrating the
--   two multiplicative wall rates along the exact exit flow, so that
--   $(P_h)_1=u m_0$ and $(P_h)_3=w m_1$. Write
--   $B_i^h=4m_i/H(P_h)$ for $i=0,1$.
--   For $Y=(2+2\alpha,u,w)$ let $h=\eta\alpha^J$.
--   All derivatives of maps with subscript $h$ hold this height fixed.
--   A cone direction is $d=(1,d_1,d_2)$ with
--   $|d_1|\leq\sqrt u$, $|d_2|\leq\sqrt w$.
--   For $y=(m,u,v,w)\in\mathbb R^4$, define
--   $$K(u,v,w)=u^2+v^2+w^2-2(uv+vw+wu),\qquad \kappa=u(v+w-u),$$
--   $$F_m=-v^2+w^2+u(v-w)-m\kappa,\qquad
--   F_u=\tfrac12(1-m^2-(v-w)^2+u^2)u,$$
--   $$F_v=(m-1-\kappa)v,\qquad F_w=(-m-1-\kappa)w,\qquad
--   F=(F_m,F_u,F_v,F_w),$$
--   and $E(m,v)=(m-1)^2+v^2$.
--
--   Write $r(m,v)=\sqrt{(m-1)^2+v^2}$ and define
--   $$g(R,v)=\sqrt{R^2-v^2},\qquad d(R,u,v,w)=g(R,v)+u(v+w-u),$$
--   $$f_R=\frac{-u(v+w-u)R-g(R,v)(u-w)^2/R}{d},$$
--   $$a_s=\frac{2g(R,v)-R^2+2vw-w^2+u^2}{2d},\qquad
--   a_w=\frac{g(R,v)-2-u(v+w-u)}d.$$
--   The exit clock rate is $\omega(y)=1-m+u(v+w-u)$, and its field is
--   $F_{\log}(y)=F(y)/\omega(y)$. Division and square roots have their total
--   real-valued Lean meanings.
--
--   For $Y=(R,u,w)$ define $E_v(Y)=(f_R,a_su,a_ww)$, evaluated at $(R,u,v,w)$.
--   The coordinate maps are $Q(m,u,v,w)=(r(m,v),u,w)$ and
--   $Q_v^{-1}(R,u,w)=(1-g(R,v),u,v,w)$.
--   For a curve $Y(s)$ set
--   $$M_i(Y,t)=\exp\int_0^t a_i(Y_0(s),Y_1(s),e^{-s},Y_2(s))\,ds
--   \quad(i=s,w).$$
--   Let $\mathcal R_{\alpha,b,A,D}$ consist of the states satisfying
--   $$7/4\leq R\leq17/4,\quad |u|,|w|\leq1/100,\quad
--   |u|+|w|\leq Ab,\quad |R-(2+2\alpha)|\leq Db.$$
--   Put
--   $$B(\alpha,b,A,D,T)=[10(\alpha+Db)+100(Ab)^2]T+100Ab+5,$$
--   $$L(\eta,\alpha,J)=\log(1/\eta)+J\log(1/\alpha).$$
--   For $0<\eta_0<1$,
--   $J\geq1$ there are $C\geq1$, $\varepsilon>0$ valid for
--   $\eta_0\leq\eta<1$, $0<\alpha\leq1$,
--   $0<b\leq\varepsilon\alpha^J$, $|u|+|w|\leq b$.
--   The tail is valid, $F=Q\circ P_h$ is $C^2$ at $Y$, and
--   $$\|dF(Y)\|\leq C,\qquad
--   \|d^2F(Y)\|\leq C L(\eta,\alpha,J).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/ExitTailHeightDerivativeBounds.lean#L11-L105

import Definitions.Def_BianchiIX_Analysis_SignedRowGrowth
import Definitions.Def_BianchiIX_TerminalConnectionData
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_TerminalConeData
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreTail
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
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
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
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

theorem BianchiIX.exists_terminal_exitReturn_two_bounds_uniform {η₀ : ℝ} (hη₀ : 0 < η₀ ∧ η₀ < 1)
    {J : ℕ} (hJ : 1 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η < 1 → (0 < α ∧ α ≤ 1) → 0 < b →
      b ≤ ε * α ^ J → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (fun Z => toExitTailState (coreTailState h Z)) Y ∧
        ‖fderiv ℝ (fun Z => toExitTailState (coreTailState h Z)) Y‖ ≤ C ∧
        ‖fderiv ℝ (fderiv ℝ (fun Z => toExitTailState (coreTailState h Z))) Y‖ ≤
          C * exitTailLength η α J := by sorry
