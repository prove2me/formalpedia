-- Prove2me | Theorems.Thm_BianchiIX_exists_normalized_event
-- name    : BianchiIX.exists_normalized_event
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T22:28:35.533223+00:00
-- url     : https://prove2.me/theorems/6eaa3156-42bc-46f8-9224-0d7b190f1d7b
-- title:
--   A locally unique transverse event with its time and endpoint derivatives
-- statement:
--   For real variables $p,s,a,b,c$, set
--   $$K=a^2+b^2+c^2-2(ab+bc+ca),\qquad S=p^2+s^2,\qquad C=S+K.$$
--   The shear components and wall rates are
--   $$P=Kp-2a^2+b^2+c^2+ab-2bc+ac,$$
--   $$Q=Ks+\sqrt{3}(-b^2+c^2+ab-ac),$$
--   $$r_1=-S+2p,\qquad r_2=-S-p+\sqrt{3}s,\qquad r_3=-S-p-\sqrt{3}s.$$
--   These functions define the normalized vacuum Bianchi IX vector field
--   $(P,Q,r_1a,r_2b,r_3c)$.
--
--   Let $X=\mathbb R^5$ with coordinates $x=(p,s,a,b,c)$ and the sup norm. Write
--   $$F(x)=(P,Q,r_1a,r_2b,r_3c),\qquad \mathcal C(x)=C(p,s,a,b,c),$$
--   and let $W=\{(p,s,a,b,c)\in X:a>0,\ b>0,\ c>0\}$.
--
--   Write $N_1(x)=a$, $N_2(x)=b$, and $N_3(x)=c$. For initial data $(x_0,t_0)$,
--   let $I_{\max}(x_0,t_0)$ be the union of all open convex domains of solutions
--   with these initial data, and let $\alpha_{x_0,t_0}$ be their compatible curve.
--   A solution $S$ has such a domain $I_S$, a curve $\alpha_S$, and
--   $\alpha_S(t_0)=x_0$.
--
--   Let $\mathcal L(X,X)$ be the continuous linear operators on $X$ and set
--   $$A(x)=dF_x,\qquad \widetilde F(x,J)=(F(x),A(x)\circ J).$$
--
--   For a fixed initial time $t_0$, put
--   $$\mathcal D_{t_0}=\{(x,t):t\in I_{\max}(x,t_0)\},\qquad
--   \Phi_{t_0}(x,t)=\alpha_{x,t_0}(t),\qquad
--   J_{x,t_0}(t)=d_x\Phi_{t_0}(x,t).$$
--
--   For $g:X\to\mathbb R$ and $p=\Phi_{t_0}(x,t)$, define
--   $$\rho=dg_p(F(p)),\qquad L=-\rho^{-1}\,dg_p\circ J_{x,t_0}(t),$$
--   $$H(v)=J_{x,t_0}(t)v+L(v)F(p).$$
--   The reciprocal in these total definitions has $0^{-1}=0$.
--   Assume $(x,t)\in\mathcal D_{t_0}$, $g$ is
--   $C^1$ at $p=\Phi_{t_0}(x,t)$, and $\rho\ne0$. There exists
--   $\tau:X\to\mathbb R$, of class $C^1$ at $x$, with
--   $$\tau(x)=t,\qquad d\tau_x=L.$$
--   For all $y$ sufficiently near $x$, one has $(y,\tau(y))\in\mathcal D_{t_0}$
--   and $g(\Phi_{t_0}(y,\tau(y)))=g(p)$. For all $(y,s)$ sufficiently
--   near $(x,t)$, one has $(y,s)\in\mathcal D_{t_0}$ and
--   $$g(\Phi_{t_0}(y,s))=g(p)\quad\Longleftrightarrow\quad\tau(y)=s.$$
--   The endpoint map $R(y)=\Phi_{t_0}(y,\tau(y))$ is $C^1$ at $x$
--   and has derivative $dR_x=H$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/Events.lean#L34-L97

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

noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

theorem BianchiIX.exists_normalized_event {x : NormalizedState} {t₀ t : ℝ} {g : NormalizedState → ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀)
    (hg : ContDiffAt ℝ 1 g (normalizedMaxCurve x t₀ t))
    (htrans : normalizedEventRate g x t₀ t ≠ 0) :
    ∃ τ : NormalizedState → ℝ, τ x = t ∧ ContDiffAt ℝ 1 τ x ∧
      HasFDerivAt τ (normalizedEventTimeDifferential g x t₀ t) x ∧
      (∀ᶠ y in 𝓝 x, τ y ∈ normalizedMaxDomain y t₀ ∧
        g (normalizedMaxCurve y t₀ (τ y)) = g (normalizedMaxCurve x t₀ t)) ∧
      (∀ᶠ z : NormalizedState × ℝ in 𝓝 (x, t), z.2 ∈ normalizedMaxDomain z.1 t₀ ∧
        (g (normalizedMaxCurve z.1 t₀ z.2) = g (normalizedMaxCurve x t₀ t) ↔ τ z.1 = z.2)) ∧
      ContDiffAt ℝ 1 (fun y => normalizedMaxCurve y t₀ (τ y)) x ∧
      HasFDerivAt (fun y => normalizedMaxCurve y t₀ (τ y)) (normalizedEventDifferential g x t₀ t) x := by sorry
