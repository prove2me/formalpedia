-- Prove2me | Theorems.Thm_BianchiIX_exists_restartSectionWeakWall_derivative
-- name    : BianchiIX.exists_restartSectionWeakWall_derivative
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T04:40:00.137229+00:00
-- url     : https://prove2.me/theorems/2fa0794d-72c6-440d-896a-94b34bff91b0
-- title:
--   Variation of a weak wall with fixed initial amplitude
-- statement:
--   Write $\Phi_t x$ for the normalized vacuum Bianchi IX flow and
--   $x_h(Z)$ for the constraint-one, negative-first-shear chart with primary
--   wall $h$ and center coordinates $Z=(v,b,c)$ (second shear and the other
--   two walls). At time $t$, denote its primary wall by $n_t$ and center by
--   $Z_t$. Set $r(Z)=\sqrt{v^2+(b-c)^2}$. For $u=\sqrt{1-h^2}$ define
--   $A=3/(2+u)$, $B=3\sqrt3 h/(2+u)^2$, $H=9(1+u)/(2(2+u)^2)$,
--   $Q_h(v,w)=(Av+Bw)^2+H^2w^2$ and $F_h(Z)=\sqrt{Q_h(v,b-c)}/\sqrt3$.
--   There is an absolute $C\ge32$. Use $h>0$,
--   $Ch\le1/4$, $0<b_0\le1/16$, $T\ge0$, $Cb_0T\le1/8$ and $0\le t\le T$.
--   At time $T$, for $\|Z\|<b_0/2$ each weak wall
--   $W_i=(Z_T)_i$, $i=1,2$, equals $Z_i m_i$ with $1/2<m_i<2$.
--   It is differentiable, and if $v_i=0$ then
--   $|DW_i[v]|\le8CT|W_i|\,\|v\|$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/RestartSectionWeakDerivative.lean#L15-L57

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_SectionRestartData
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
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
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

theorem BianchiIX.exists_restartSectionWeakWall_derivative :
    ∃ C ≥ (32 : ℝ), ∀ h b T : ℝ,
      0 < h → C * h ≤ 1 / 4 → (0 < b ∧ b ≤ 1 / 16) → 0 ≤ T → C * b * T ≤ 1 / 8 →
      ∀ Z : RestartCenterState, ‖Z‖ < b / 2 → ∀ i : Fin 2,
        restartSectionCenterFlow h T Z i.succ = Z i.succ * restartSectionWeakMultiplier h T i Z ∧
        (1 / 2 < restartSectionWeakMultiplier h T i Z ∧ restartSectionWeakMultiplier h T i Z < 2) ∧
        DifferentiableAt ℝ (fun W => restartSectionCenterFlow h T W i.succ) Z ∧
        ∀ v : RestartCenterState, v i.succ = 0 →
          |fderiv ℝ (fun W => restartSectionCenterFlow h T W i.succ) Z v| ≤
            8 * C * T * |restartSectionCenterFlow h T Z i.succ| * ‖v‖ := by sorry
