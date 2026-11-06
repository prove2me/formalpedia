-- Prove2me | Theorems.Thm_BianchiIX_exists_referenceCore_firstReturn_two
-- name    : BianchiIX.exists_referenceCore_firstReturn_two
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T23:13:43.457402+00:00
-- url     : https://prove2.me/theorems/2bcd7637-362a-4b0b-b576-4ee5dbdb16d8
-- title:
--   The reference first-return time and map are twice continuously differentiable
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
--   For real $k,t$, define the boundary pulse
--   $$\beta_k(t)=(m_k(t),0,v_k(t),0)
--   =\left(1-k\tanh(kt),0,\frac{k}{\cosh(kt)},0\right).$$
--
--   Set
--   $$h_k=\frac{\operatorname{arcosh}k}{k},\qquad
--   T_k=\frac{(k^2+4)\operatorname{arcosh}k}{3k},\qquad
--   d_k=\sqrt{k^2-1},$$
--   $$H_k(t)=\frac{k^2+4}{6}t-\frac13\log\cosh(kt).$$
--   Use the total real conventions $x/0=0$, $\sqrt{x}=\sqrt{\max(x,0)}$,
--   $\log0=0$, and $\log x=\log|x|$ for $x<0$, with
--   $\operatorname{arcosh}x=\log(x+\sqrt{x^2-1})$.
--   Write $\alpha_{x,0}$ for the maximal normalized solution starting at $x$
--   at time zero, with domain $I_{\max}(x,0)$.
--
--   The positive transverse modes and crossing multipliers are
--   $$M_{k,r}(t)=e^{-rt}\cosh(kt),\qquad
--   \mu_u(k)=e^{-k\operatorname{arcosh}k},\qquad
--   \mu_w(k)=e^{-4\operatorname{arcosh}k/k}.$$
--
--   Define the variational velocity with tangent forcing by
--   $$V_k(t,\xi,a)=dF_{\beta_k(t)}\xi+aF(\beta_k(t)).$$
--   For $\xi=(\xi_m,\xi_u,\xi_v,\xi_w)$, set
--   $$J_k(t,\xi)=2(m_k(t)-1)\xi_m+2v_k(t)\xi_v-4v_k(t)\xi_u,$$
--   $$P_k\xi=(\xi_m-\xi_v/d_k,\xi_u,0,\xi_w).$$
--
--   Write $G(y)=6F(y)/D(y)$ for the projective vector field in normalized time.
--
--   Write $X=\mathbb R^5$, $Y=\mathbb R^4$, and let $\alpha_{x,t_0}$ be the
--   maximal solution of $\alpha'=N(\alpha)$ with initial value $x$ at $t_0$
--   and domain $I_{\max}(x,t_0)$. Put
--   $$J_{x,t_0}(t)=d_x\alpha_{x,t_0}(t),\qquad
--   \Psi_{t_0}(y,t)=\Pi(\alpha_{\Xi(y),t_0}(t)),$$
--   $$\mathcal J_{y,t_0}(t)=d\Pi_{\alpha_{\Xi(y),t_0}(t)}
--   \circ J_{\Xi(y),t_0}(t)\circ d\Xi_y.$$
--
--   Define $x_k^-=\Xi(\beta_k(-h_k))$, $x_k^+=\Xi(\beta_k(h_k))$,
--   and the active-wall observable $g(x)=(\Pi(x))_2$, with zero-based indices.
--   For $x_*=\alpha_{x,t_0}(t)$, set
--   $$\rho_{x,t_0,t}=dg_{x_*}(N(x_*)),\qquad
--   \mathscr L_{x,t_0,t}=-\rho_{x,t_0,t}^{-1}dg_{x_*}\circ J_{x,t_0}(t),$$
--   $$\mathscr H_{x,t_0,t}(v)=J_{x,t_0}(t)v+
--   \mathscr L_{x,t_0,t}(v)N(x_*).$$
--   Here $0^{-1}=0$ in the total definitions.
--
--   Define the clock based at entry and the actual projective variation by
--   $$c_k(t)=H_k(t)-H_k(-h_k),\qquad
--   W_k(w,t)=\mathcal J_{\beta_k(-h_k),0}(c_k(t))w.$$
--
--   Let $Z=\mathbb R^3$ with its finite-product norm and define
--   $$e(z_0,z_1,z_2)=(z_0,z_1,1,z_2),\qquad
--   q(m,u,v,w)=(m,u,w),\qquad \chi=\Xi\circ e,$$
--   $$z_k^-=(1+d_k,0,0),\qquad z_k^+=(1-d_k,0,0).$$
--   For $k>1$, let
--   $$A_k(v_0,v_1,v_2)=
--   \left(-v_0+\frac2{d_k}(1-\mu_u(k))v_1,\mu_u(k)v_1,\mu_w(k)v_2\right).$$
--   For every $k>1$ there exist
--   $\tau:Z\to\mathbb R$ and $P:Z\to Z$, both $C^2$ at $z_k^-$, with
--   $$\tau(z_k^-)=T_k,\qquad P(z_k^-)=z_k^+,\qquad dP_{z_k^-}=A_k.$$
--   For all $z$ sufficiently near $z_k^-$, $\tau(z)$ is the least element of
--   $$\{t>0:t\in I_{\max}(\chi(z),0),\ g(\alpha_{\chi(z),0}(t))=1\}.$$
--   Throughout $[0,\tau(z)]$ the flow is defined and its chart factor
--   $1+(\alpha_{\chi(z),0}(t))_0$ is positive. The active wall is strictly
--   greater than one for $0<t<\tau(z)$, and at the return
--   $$\rho_{\chi(z),0,\tau(z)}<0,\qquad
--   \Pi(\alpha_{\chi(z),0}(\tau(z)))=e(P(z)).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/ReferenceSecondReturn.lean#L12-L79

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ReferencePulse
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ReferenceReturn
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ReferenceEvents
import Definitions.Def_BianchiIX_Dynamics_ReferenceSectionMap
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Tactic.NormNum
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
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

theorem BianchiIX.exists_referenceCore_firstReturn_two {k : ℝ} (hk : 1 < k) :
    ∃ (τ : CoreCoordinates → ℝ) (P : CoreCoordinates → CoreCoordinates),
      τ (referenceCoreInput k) = referenceNormalizedTime k ∧
      P (referenceCoreInput k) = referenceCoreOutput k ∧
      ContDiffAt ℝ 2 τ (referenceCoreInput k) ∧ ContDiffAt ℝ 2 P (referenceCoreInput k) ∧
      (∀ᶠ z in 𝓝 (referenceCoreInput k),
        IsLeast {t : ℝ | 0 < t ∧ t ∈ normalizedMaxDomain (coreSectionChart z) 0 ∧
          projectiveActiveWall (normalizedMaxCurve (coreSectionChart z) 0 t) = 1} (τ z) ∧
        (∀ t ∈ Icc 0 (τ z), t ∈ normalizedMaxDomain (coreSectionChart z) 0 ∧
          0 < 1 + normalizedMaxCurve (coreSectionChart z) 0 t 0) ∧
        (∀ t ∈ Ioo 0 (τ z), 1 < projectiveActiveWall (normalizedMaxCurve (coreSectionChart z) 0 t)) ∧
        normalizedEventRate projectiveActiveWall (coreSectionChart z) 0 (τ z) < 0 ∧
        toProjectiveState (normalizedMaxCurve (coreSectionChart z) 0 (τ z)) = coreSectionEmbedding (P z)) ∧
      (∀ v : CoreCoordinates, fderiv ℝ P (referenceCoreInput k) v =
        ![-v 0 + (2 / Real.sqrt (k ^ 2 - 1)) * (1 - Real.exp (-k * Real.arcosh k)) * v 1,
          Real.exp (-k * Real.arcosh k) * v 1, Real.exp (-4 * Real.arcosh k / k) * v 2]) := by sorry
