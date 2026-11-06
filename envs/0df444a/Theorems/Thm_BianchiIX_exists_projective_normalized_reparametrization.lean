-- Prove2me | Theorems.Thm_BianchiIX_exists_projective_normalized_reparametrization
-- name    : BianchiIX.exists_projective_normalized_reparametrization
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T21:35:20.123795+00:00
-- url     : https://prove2.me/theorems/6e21c693-18a5-45d6-84a8-c8138c5440ed
-- title:
--   Lifting a projective solution to the maximal normalized flow
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
--   For $a:\mathbb R\to\mathbb R$ and $t_0\in\mathbb R$,
--   define the oriented integral clock
--   $$c_{a,t_0}(t)=\int_{t_0}^t a(u)\,du.$$
--
--   For initial data $(x_0,t_0)$, let $\alpha_{x_0,t_0}$ denote the maximal
--   normalized solution with domain $I_{\max}(x_0,t_0)$. Define
--   $$a_{x_0,t_0}(t)=1+(\alpha_{x_0,t_0}(t))_0.$$
--   Let $I$ be open and convex,
--   $s\in I$, and $\beta'(\tau)=F(\beta(\tau))$ with $D(\beta(\tau))>0$
--   throughout $I$. There is an open partial homeomorphism $e$ with source
--   $I$, forward map
--   $$e(\tau)=\int_s^\tau D(\beta(u))/6\,du,$$
--   and target equal to this integral's image of $I$. The target is convex
--   and contains zero, $e^{-1}(0)=s$, and $e$ is strictly increasing on $I$.
--   For $x_0=\Xi(\beta(s))$, its target is contained in $I_{\max}(x_0,0)$,
--   and for every $t$ in that target,
--   $$\Xi(\beta(e^{-1}(t)))=\alpha_{x_0,0}(t),\qquad
--   \Pi(\alpha_{x_0,0}(t))=\beta(e^{-1}(t)).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/ProjectiveClock.lean#L73-L127

import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveClock
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
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
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

theorem BianchiIX.exists_projective_normalized_reparametrization
    {β : ℝ → ProjectiveState} {I : Set ℝ} {s : ℝ}
    (hI : Convex ℝ I) (ho : IsOpen I) (hs : s ∈ I)
    (hβ : ∀ τ ∈ I, HasDerivAt β (projectiveField (β τ)) τ)
    (hD : ∀ τ ∈ I, 0 < projectiveStateDenom (β τ)) :
    ∃ e : OpenPartialHomeomorph ℝ ℝ,
      e.source = I ∧
      (∀ τ, e τ = integralClock (fun u => projectiveStateDenom (β u) / 6) s τ) ∧
      e.target = integralClock (fun u => projectiveStateDenom (β u) / 6) s '' I ∧
      Convex ℝ e.target ∧ 0 ∈ e.target ∧ e.symm 0 = s ∧
      StrictMonoOn e I ∧
      e.target ⊆ normalizedMaxDomain (fromProjectiveState (β s)) 0 ∧
      (∀ t ∈ e.target,
        fromProjectiveState (β (e.symm t)) =
          normalizedMaxCurve (fromProjectiveState (β s)) 0 t ∧
        toProjectiveState (normalizedMaxCurve (fromProjectiveState (β s)) 0 t) = β (e.symm t)) := by sorry
