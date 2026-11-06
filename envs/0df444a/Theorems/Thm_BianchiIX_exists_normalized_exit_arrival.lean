-- Prove2me | Theorems.Thm_BianchiIX_exists_normalized_exit_arrival
-- name    : BianchiIX.exists_normalized_exit_arrival
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T18:03:47.94221+00:00
-- url     : https://prove2.me/theorems/5ebb5589-d3ee-42ea-ba1e-4916a7ccaea5
-- title:
--   Existence of the power-scaled exit event in the exact Einstein flow
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
--   Write $r(m,v)=\sqrt{(m-1)^2+v^2}$ and $g_*(x)=(\Pi(x))_v$.
--   The closed exit region $\mathcal E_h$ is defined by
--   $$m\leq0,\quad7/4\leq r(m,v)\leq17/4,\quad
--   |u|,|w|\leq1/100,\quad h\leq v\leq1.$$
--   Let $L(\eta,\alpha,J)=\log(1/\eta)+J\log(1/\alpha)$.
--   Fix $0<\eta<1$ and $J\geq1$. There exist
--   $A\geq2$, $\varepsilon>0$ such that, for $\mathcal C(x)=1$,
--   $t_0\leq s$, $0<\alpha\leq1$, $0<b\leq\varepsilon\alpha^J$,
--   and positive chart clock at $s$, the following is true. Put
--   $\beta=\Pi\circ\alpha_{x,t_0}$ and suppose
--   $\beta_m(s)<0$, $\beta_v(s)=1$, $r(\beta_m(s),1)=2+2\alpha$,
--   and $|\beta_u(s)|+|\beta_w(s)|\leq b$.
--   There is $t>s$ with $\beta_v(t)=\eta\alpha^J$ and
--   $t-s\leq16L(\eta,\alpha,J)$. Throughout $[s,t]$,
--   $$1+(\alpha_{x,t_0})_0\geq1/16,\quad\beta\in\mathcal E_{\eta\alpha^J},$$
--   $$|\beta_u|+|\beta_w|\leq Ab/2,\quad
--   |r(\beta_m,\beta_v)-(2+2\alpha)|\leq40Ab,\quad
--   r(\beta_m,\beta_v)>2+\alpha,\quad |\beta_u|\leq\beta_v/2.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/ExitExistence.lean#L36-L136

import Definitions.Def_BianchiIX_TerminalConnectionData
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
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
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

theorem BianchiIX.exists_normalized_exit_arrival {η : ℝ} (hη : 0 < η ∧ η < 1) {J : ℕ} (hJ : 1 ≤ J) :
    ∃ A ≥ (2 : ℝ), ∃ ε > (0 : ℝ), ∀ (x : NormalizedState) (t₀ s α b : ℝ),
      stateConstraint x = 1 → t₀ ≤ s → (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ J →
      0 < 1 + normalizedMaxCurve x t₀ s 0 →
      let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
      β s 0 < 0 → β s 2 = 1 → coreRadius (β s 0) (β s 2) = 2 + 2 * α →
      |β s 1| + |β s 3| ≤ b →
      ∃ t > s, β t 2 = η * α ^ J ∧
        (∀ u ∈ Icc s t, 1 / 16 ≤ 1 + normalizedMaxCurve x t₀ u 0 ∧
          exitPhysicalRegion (η * α ^ J) (β u)) ∧
        t - s ≤ 16 * exitTailLength η α J ∧
        (∀ u ∈ Icc s t, |β u 1| + |β u 3| ≤ A * b / 2 ∧
          |coreRadius (β u 0) (β u 2) - coreRadius (β s 0) (β s 2)| ≤ 40 * A * b ∧
          2 + α < coreRadius (β u 0) (β u 2) ∧ |β u 1| ≤ β u 2 / 2) := by sorry
