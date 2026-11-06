-- Prove2me | Theorems.Thm_BianchiIX_eventually_activeWall_first_downcrossing
-- name    : BianchiIX.eventually_activeWall_first_downcrossing
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T07:06:57.0642+00:00
-- url     : https://prove2.me/theorems/048ca936-6518-4285-b727-9842ca734103
-- title:
--   A locally unique downward crossing remains the first downward crossing
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
--   Let $g(x)=(\Pi(x))_v$ and put
--   $$\rho(x,t_0,t)=dg_{\alpha_{x,t_0}(t)}N(\alpha_{x,t_0}(t)),\qquad
--   A(x,t_0,t)=1+(\alpha_{x,t_0}(t))_0.$$
--   Fix $x,t_0,s,\eta$ and a function $\tau:X\to\mathbb R$
--   continuous at $x$, with $s<\tau(x)$. Suppose the reference flow lies in its
--   maximal domain with $A(x,t_0,t)>0$ on $[s,\tau(x)]$. At each earlier time
--   in $[s,\tau(x))$, assume either $g(\alpha_{x,t_0}(t))\ne\eta$ or
--   $\rho(x,t_0,t)>0$. For every $y$ sufficiently near $x$, assume
--   $$g(\alpha_{y,t_0}(\tau(y)))=\eta,\qquad \rho(y,t_0,\tau(y))<0.$$
--   Assume also that, for $(y,t)$ near $(x,\tau(x))$, equality
--   $g(\alpha_{y,t_0}(t))=\eta$ implies $t=\tau(y)$. Then, for $y$ near $x$,
--   $\tau(y)$ is the least time $t>s$ in the maximal domain at which the
--   height is $\eta$ and the event rate is negative. The whole interval
--   $[s,\tau(y)]$ stays in that domain with positive clock $A$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/ActiveWallDowncrossing.lean#L10-L70

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_Events
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

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

theorem BianchiIX.eventually_activeWall_first_downcrossing {x : NormalizedState}
    {τ : NormalizedState → ℝ} {t₀ s η : ℝ}
    (hcτ : ContinuousAt τ x) (hst : s < τ x)
    (hreg : ∀ t ∈ Icc s (τ x), t ∈ normalizedMaxDomain x t₀ ∧ 0 < 1 + normalizedMaxCurve x t₀ t 0)
    (hbefore : ∀ t ∈ Ico s (τ x),
      projectiveActiveWall (normalizedMaxCurve x t₀ t) ≠ η ∨
        0 < normalizedEventRate projectiveActiveWall x t₀ t)
    (hhit : ∀ᶠ y in 𝓝 x, projectiveActiveWall (normalizedMaxCurve y t₀ (τ y)) = η ∧
      normalizedEventRate projectiveActiveWall y t₀ (τ y) < 0)
    (huniq : ∀ᶠ z : NormalizedState × ℝ in 𝓝 (x, τ x),
      projectiveActiveWall (normalizedMaxCurve z.1 t₀ z.2) = η → τ z.1 = z.2) :
    ∀ᶠ y in 𝓝 x,
      IsLeast {t | s < t ∧ t ∈ normalizedMaxDomain y t₀ ∧
        projectiveActiveWall (normalizedMaxCurve y t₀ t) = η ∧
        normalizedEventRate projectiveActiveWall y t₀ t < 0} (τ y) ∧
      (∀ t ∈ Icc s (τ y), t ∈ normalizedMaxDomain y t₀ ∧ 0 < 1 + normalizedMaxCurve y t₀ t 0) := by sorry
