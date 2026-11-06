-- Prove2me | Theorems.Thm_BianchiIX_fromExitTailState_fderiv_bound
-- name    : BianchiIX.fromExitTailState_fderiv_bound
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T18:59:38.774228+00:00
-- url     : https://prove2.me/theorems/8283380e-7f8c-4acd-b7bd-6031482c6e62
-- title:
--   Bounded derivative of the inverse radial exit coordinates
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
--
--   For $Y=(R,u,w)$ define $E_v(Y)=(f_R,a_su,a_ww)$, evaluated at $(R,u,v,w)$.
--   The coordinate maps are $Q(m,u,v,w)=(r(m,v),u,w)$ and
--   $Q_v^{-1}(R,u,w)=(1-g(R,v),u,v,w)$.
--   For a curve $Y(s)$ set
--   $$M_i(Y,t)=\exp\int_0^t a_i(Y_0(s),Y_1(s),e^{-s},Y_2(s))\,ds
--   \quad(i=s,w).$$
--   Let $\mathcal R_{\alpha,b,A,D}$ consist of the states satisfying
--   $$7/4\leq R\leq17/4,\quad |u|,|w|\leq1/100,\quad
--   |u|+|w|\leq Ab,\quad |R-(2+2\alpha)|\leq Db.$$
--   Put
--   $$B(\alpha,b,A,D,T)=[10(\alpha+Db)+100(Ab)^2]T+100Ab+5,$$
--   $$L(\eta,\alpha,J)=\log(1/\eta)+J\log(1/\alpha).$$
--   For $Y_0\geq7/4$ and $|h|\leq1$,
--   the map $Q_h^{-1}$ is $C^2$ at $Y$ and
--   $\|dQ_h^{-1}(Y)\|\leq2$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/ExitTailReconstruction.lean#L12-L67

import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
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
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Module
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
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open BianchiIX
open Filter
open scoped Topology

theorem BianchiIX.fromExitTailState_fderiv_bound {h : ℝ} {Y : ExitTailState}
    (hR : 7 / 4 ≤ Y 0) (hh : |h| ≤ 1) :
    ContDiffAt ℝ 2 (fromExitTailState h) Y ∧ ‖fderiv ℝ (fromExitTailState h) Y‖ ≤ 2 := by sorry
