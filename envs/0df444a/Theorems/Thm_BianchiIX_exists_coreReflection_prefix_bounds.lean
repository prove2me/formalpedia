-- Prove2me | Theorems.Thm_BianchiIX_exists_coreReflection_prefix_bounds
-- name    : BianchiIX.exists_coreReflection_prefix_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T00:35:39.624053+00:00
-- url     : https://prove2.me/theorems/a55773ca-9c59-4781-8909-1769fa0d8995
-- title:
--   Finite core-reflection orbits pay for errors by amplitude loss
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
--   There are $0<\varepsilon\leq10^{-4}$,
--   $C>0$, $0<c\leq1/2$ with the following property. Let $n\in\mathbb N$
--   and $Y_j$ satisfy $0<(Y_0)_1,(Y_0)_2\leq\varepsilon/(Y_0)_0$,
--   and, for $j<n$, $(Y_j)_0\geq2$, $F(Y_j)_0\geq31/8$,
--   $Y_{j+1}=G(Y_j)$. Put $b_j=(Y_j)_1+(Y_j)_2$,
--   $A=C(1+c/2)/c$, $D=C(1+c/4)/(c/2)$.
--   All walls of $Y_j$ are positive for $j\leq n$, and for every $p>0$,
--   $$\sum_{j<n}\frac{b_j^p}{(Y_j)_0}
--   \leq\frac{1+pc/2}{pc}(b_0^p-b_n^p).$$
--   The sum of $|F(Y_j)_0-(Y_j)_0|+|(Y_{j+1})_0-(F(Y_j)_0-2)|$
--   is at most $A(b_0-b_n)$; so is $|(Y_n)_0-((Y_0)_0-2n)|$.
--   One has $G^n(Y_0)=Y_n$, $G^n$ is $C^1$ at $Y_0$, and every step
--   has positive physical time $t_G(Y_j)$ and the exact reflected flow identity.
--   For each initial cone direction, $G^n$ has the positive cone property and
--   $$|\log(dG^n(Y_0)v)_0|\leq D(\sqrt{b_0}-\sqrt{b_n}).$$
--   If $(Y_n)_0\geq2$, put $Z=F(Y_n)$, $B=Z_1+Z_2$ and $H=F\circ G^n$.
--   The last core return is valid, $H$ and $T\circ G^n$ are $C^1$ at $Y_0$,
--   $Z_1,Z_2>0$, $B\leq b_0$,
--   $$|Z_0-((Y_0)_0-2n)|\leq A(b_0-B).$$
--   The map $H$ has the positive cone property, with
--   $|\log(dH(Y_0)v)_0|\leq D(\sqrt{b_0}-\sqrt B)$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/CoreReflectionPrefix.lean#L9-L205

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

noncomputable section
open BianchiIX

theorem BianchiIX.exists_coreReflection_prefix_bounds :
    ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), c ≤ 1 / 2 ∧
      ∀ (n : ℕ) (Y : ℕ → CoreAngleState),
        let F := coreReturnState coreRadiusReturnTime
        let G := coreReflectionState coreRadiusReturnTime
        let b := fun j => Y j 1 + Y j 2
        (0 < Y 0 1 ∧ Y 0 1 ≤ ε / Y 0 0) → (0 < Y 0 2 ∧ Y 0 2 ≤ ε / Y 0 0) →
        (∀ j < n, 2 ≤ Y j 0 ∧ 31 / 8 ≤ F (Y j) 0) →
        (∀ j < n, Y (j + 1) = G (Y j)) →
        (∀ j ≤ n, ∀ i : Fin 2, 0 < Y j i.succ) ∧
        (∀ p > (0 : ℝ), ∑ j ∈ Finset.range n, (b j) ^ p / Y j 0 ≤
          ((1 + p * c / 2) / (p * c)) * ((b 0) ^ p - (b n) ^ p)) ∧
        (∑ j ∈ Finset.range n, (|F (Y j) 0 - Y j 0| + |Y (j + 1) 0 - (F (Y j) 0 - 2)|)) ≤
          C * ((1 + c / 2) / c) * (b 0 - b n) ∧
        |Y n 0 - (Y 0 0 - 2 * n)| ≤ C * ((1 + c / 2) / c) * (b 0 - b n) ∧
        G^[n] (Y 0) = Y n ∧ (ContDiffAt ℝ 1 (G^[n]) (Y 0) ∧
          ∀ j < n, 0 < coreReflectionTime (Y j) ∧
            coreRadiusEntry (Y (j + 1)) = projectiveReflection
              (projectiveOriginalFlow (coreRadiusEntry (Y j)) 0 (coreReflectionTime (Y j)))) ∧
        (∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 0 1) → |v 2| ≤ Real.sqrt (Y 0 2) →
          let d := fderiv ℝ (G^[n]) (Y 0) v
          0 < d 0 ∧ |Real.log (d 0)| ≤
            C * ((1 + c / 4) / (c / 2)) * (Real.sqrt (b 0) - Real.sqrt (b n)) ∧
            ∀ i : Fin 2, |d i.succ| ≤ Real.sqrt (Y n i.succ) * d 0) ∧
        (2 ≤ Y n 0 →
          let Z := F (Y n)
          let B := Z 1 + Z 2
          let J := F ∘ G^[n]
          coreRadiusReturnValid (Y n) ∧ ContDiffAt ℝ 1 J (Y 0) ∧
          ContDiffAt ℝ 1 (coreRadiusReturnTime ∘ G^[n]) (Y 0) ∧
          (∀ i : Fin 2, 0 < Z i.succ) ∧ B ≤ b 0 ∧
          |Z 0 - (Y 0 0 - 2 * n)| ≤ C * ((1 + c / 2) / c) * (b 0 - B) ∧
          ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 0 1) → |v 2| ≤ Real.sqrt (Y 0 2) →
            let d := fderiv ℝ J (Y 0) v
            0 < d 0 ∧ |Real.log (d 0)| ≤
              C * ((1 + c / 4) / (c / 2)) * (Real.sqrt (b 0) - Real.sqrt B) ∧
              ∀ i : Fin 2, |d i.succ| ≤ Real.sqrt (Z i.succ) * d 0) := by sorry
