-- Prove2me | Theorems.Thm_BianchiIX_exists_large_core_traversal
-- name    : BianchiIX.exists_large_core_traversal
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T00:46:30.71706+00:00
-- url     : https://prove2.me/theorems/38b1e354-90fc-4b6a-8329-d8cca6b34f66
-- title:
--   A complete nonlinear large-core traversal with quantitative exit estimates
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
--   For fixed $x,t_0$, write
--   $$\beta(q)=\Pi(\alpha_{x,t_0}(q))=(m(q),u(q),v(q),w(q)),\qquad
--   A(q)=1+(\alpha_{x,t_0}(q))_0,$$
--   $$r(q)=r(m(q),v(q)),\qquad\theta(q)=\theta(m(q),v(q)),\qquad
--   \tau_s(q)=\int_s^q A(h)\,dh.$$
--   Let $k\geq6$ and
--   $0\leq u_0,w_0\leq\varepsilon_k$. Set
--   $$y=(1+\sqrt{k^2-1},u_0,1,w_0),\quad x=\Xi(y),\quad t_0=0.$$
--   There is $T>0$ which is the least time $t>0$ with $v(t)=1$.
--   For every $q\in[0,T]$, $A(q)>0$ and $\beta(q)\in\mathcal K_k$.
--   At the exit,
--   $$m(T)<1,\quad\theta(T)>0,\quad v'(T)<0,$$
--   $$|r(T)-k|\leq\frac{16}{k}(u_0+w_0^2),\quad
--   u(T)\leq e^{-k/40}u_0,\quad w(T)\leq e^{-1/(2k)}w_0,$$
--   $$\frac1{4k}\leq\tau_0(T)\leq\frac{4\log(4k)}k,
--   \qquad T\leq2k\log(4k).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/LargeCoreReturn.lean#L10-L82

import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ProjectiveClock
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
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
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open BianchiIX
open Set

theorem BianchiIX.exists_large_core_traversal {k u w : ℝ} (hk : 6 ≤ k)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k) :
    let y : ProjectiveState := ![1 + Real.sqrt (k ^ 2 - 1), u, 1, w]
    let x := fromProjectiveState y
    let β := fun t => toProjectiveState (normalizedMaxCurve x 0 t)
    ∃ T > 0,
      IsLeast {t | 0 < t ∧ β t 2 = 1} T ∧
      (∀ t ∈ Icc 0 T, 0 < 1 + normalizedMaxCurve x 0 t 0 ∧ coreRegion k (β t)) ∧
      β T 0 < 1 ∧ 0 < coreAngle (β T 0) (β T 2) ∧ deriv (fun t => β t 2) T < 0 ∧
      |coreRadius (β T 0) (β T 2) - k| ≤ 16 / k * (u + w ^ 2) ∧
      β T 1 ≤ Real.exp (-k / 40) * u ∧ β T 3 ≤ Real.exp (-1 / (2 * k)) * w ∧
      1 / (4 * k) ≤ integralClock (normalizedProjectiveRate x 0) 0 T ∧
      integralClock (normalizedProjectiveRate x 0) 0 T ≤ 4 * Real.log (4 * k) / k ∧
      T ≤ 2 * k * Real.log (4 * k) := by sorry
