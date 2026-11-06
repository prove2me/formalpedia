-- Prove2me | Theorems.Thm_BianchiIX_referenceForcedVariation_transverse
-- name    : BianchiIX.referenceForcedVariation_transverse
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T22:02:14.688257+00:00
-- url     : https://prove2.me/theorems/bb7d9b67-2360-49d0-8176-cf6d35129071
-- title:
--   Transverse solutions in the presence of tangent forcing
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
--   Let $I$ be convex and suppose
--   $\xi'(u)=V_k(u,\xi(u),a(u))$ on $I$. For $s,t\in I$,
--   $$\xi_u(t)=\xi_u(s)\frac{M_{k,k^2/2}(t)}{M_{k,k^2/2}(s)},\qquad
--   \xi_w(t)=\xi_w(s)\frac{M_{k,2}(t)}{M_{k,2}(s)}.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/ReferenceScattering.lean#L50-L70

import Definitions.Def_BianchiIX_Dynamics_ProjectiveLinearization
import Definitions.Def_BianchiIX_Dynamics_ReferenceVariation
import Definitions.Def_BianchiIX_Dynamics_ReferenceScattering
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
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique

noncomputable section
open BianchiIX
open Set

theorem BianchiIX.referenceForcedVariation_transverse {I : Set ℝ} (hI : Convex ℝ I)
    {k : ℝ} {xi : ℝ → ProjectiveState} {a : ℝ → ℝ}
    (hxi : ∀ t ∈ I, HasDerivAt xi (referenceVariationVelocity k t (xi t) (a t)) t)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    xi t 1 = xi s 1 * (referenceTransverseMode k (k ^ 2 / 2) t /
      referenceTransverseMode k (k ^ 2 / 2) s) ∧
    xi t 3 = xi s 3 * (referenceTransverseMode k 2 t / referenceTransverseMode k 2 s) := by sorry
