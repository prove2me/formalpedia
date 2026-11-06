-- Prove2me | Theorems.Thm_BianchiIX_referenceTail_normalized_segment
-- name    : BianchiIX.referenceTail_normalized_segment
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T04:41:22.662082+00:00
-- url     : https://prove2.me/theorems/e110a7d3-6b22-41a3-aea5-9ffcb2681212
-- title:
--   The finite reference tail is an exact segment of the maximal Einstein flow
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
--   Write $X=\mathbb R^5$, $Y=\mathbb R^4$, and let $\alpha_{x,t_0}$ be the
--   maximal solution of $\alpha'=N(\alpha)$ with initial value $x$ at $t_0$
--   and domain $I_{\max}(x,t_0)$. Put
--   $$J_{x,t_0}(t)=d_x\alpha_{x,t_0}(t),\qquad
--   \Psi_{t_0}(y,t)=\Pi(\alpha_{\Xi(y),t_0}(t)),$$
--   $$\mathcal J_{y,t_0}(t)=d\Pi_{\alpha_{\Xi(y),t_0}(t)}
--   \circ J_{\Xi(y),t_0}(t)\circ d\Xi_y.$$
--
--   Define the projective height time and normalized tail duration by
--   $$s_\eta(k)=\frac{\operatorname{arcosh}(k/\eta)}k,\qquad
--   \Delta_\eta(k)=\int_{h_k}^{s_\eta(k)}\frac{D(\beta_k(s))}{6}\,ds.$$
--   Write $x_k^+=\Xi(\beta_k(h_k))$, $g(x)=(\Pi(x))_v$, and
--   $\rho(x,t)=dg_{\alpha_{x,0}(t)}N(\alpha_{x,0}(t))$.
--   For $k>1$ and $0<\eta<1$,
--   $\Delta_\eta(k)>0$ and
--   $$\alpha_{x_k^+,0}(\Delta_\eta(k))
--   =\Xi(1-\sqrt{k^2-\eta^2},0,\eta,0).$$
--   For every $t\in[0,\Delta_\eta(k)]$,
--   $$t\in I_{\max}(x_k^+,0),\qquad
--   1+(\alpha_{x_k^+,0}(t))_0>0,\qquad
--   \rho(x_k^+,t)<0,\qquad (\Pi(\alpha_{x_k^+,0}(t)))_w=0.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/ReferenceTail.lean#L64-L115

import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ReferenceEvents
import Definitions.Def_BianchiIX_Dynamics_ReferenceTail
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

noncomputable section
open BianchiIX
open Set

theorem BianchiIX.referenceTail_normalized_segment {k η : ℝ} (hk : 1 < k) (hη : 0 < η ∧ η < 1) :
    0 < referenceTailTime k η ∧
      normalizedMaxCurve (referenceExitState k) 0 (referenceTailTime k η) =
        fromProjectiveState ![1 - Real.sqrt (k ^ 2 - η ^ 2), 0, η, 0] ∧
      ∀ t ∈ Icc 0 (referenceTailTime k η),
        t ∈ normalizedMaxDomain (referenceExitState k) 0 ∧
        0 < 1 + normalizedMaxCurve (referenceExitState k) 0 t 0 ∧
        normalizedEventRate projectiveActiveWall (referenceExitState k) 0 t < 0 ∧
        toProjectiveState (normalizedMaxCurve (referenceExitState k) 0 t) 3 = 0 := by sorry
