-- Prove2me | Theorems.Thm_BianchiIX_exists_scaled_exitLog_reparametrization
-- name    : BianchiIX.exists_scaled_exitLog_reparametrization
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T17:56:37.527186+00:00
-- url     : https://prove2.me/theorems/7d3d4124-ec99-48d4-82e6-0c984e6082eb
-- title:
--   Positive logarithmic clock for an exact exit trajectory
-- statement:
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
--   Let $I$ be an open convex interval containing
--   $s$. Assume $a$ is continuous and positive on $I$, and
--   $\beta'(t)=a(t)F(\beta(t))$, $\beta_v(t)>0$, $\omega(\beta(t))>0$
--   there. There is an open partial homeomorphism $e$ with source $I$,
--   convex target containing zero, $e^{-1}(0)=s$, strictly increasing on $I$,
--   and $e(t)=\log\beta_v(s)-\log\beta_v(t)$. For every $z$ in its target,
--   $$\frac{d}{dz}e^{-1}(z)=\frac1{a(e^{-1}(z))\omega(\beta(e^{-1}(z)))},$$
--   $$\beta_v(e^{-1}(z))=\beta_v(s)e^{-z},\qquad
--   \frac{d}{dz}\beta(e^{-1}(z))=F_{\log}(\beta(e^{-1}(z))).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/ExitClock.lean#L41-L95

import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Definitions.Def_BianchiIX_TerminalConnectionData
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

noncomputable section
open BianchiIX
open Set

theorem BianchiIX.exists_scaled_exitLog_reparametrization {β : ℝ → ProjectiveState} {a : ℝ → ℝ}
    {I : Set ℝ} {s : ℝ} (hI : Convex ℝ I) (ho : IsOpen I) (hs : s ∈ I)
    (ha : ContinuousOn a I) (hapos : ∀ t ∈ I, 0 < a t)
    (hβ : ∀ t ∈ I, HasDerivAt β (a t • projectiveField (β t)) t)
    (hv : ∀ t ∈ I, 0 < β t 2) (hD : ∀ t ∈ I, 0 < exitClockRate (β t)) :
    ∃ e : OpenPartialHomeomorph ℝ ℝ,
      e.source = I ∧
      (∀ t ∈ I, e t = Real.log (β s 2) - Real.log (β t 2)) ∧
      Convex ℝ e.target ∧ 0 ∈ e.target ∧ e.symm 0 = s ∧ StrictMonoOn e I ∧
      (∀ z ∈ e.target,
        HasDerivAt e.symm (1 / (a (e.symm z) * exitClockRate (β (e.symm z)))) z ∧
        β (e.symm z) 2 = β s 2 * Real.exp (-z) ∧
        HasDerivAt (fun u => β (e.symm u)) (exitLogField (β (e.symm z))) z) := by sorry
