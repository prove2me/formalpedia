-- Prove2me | Theorems.Thm_BianchiIX_exists_restartSectionMixedFlow_derivative
-- name    : BianchiIX.exists_restartSectionMixedFlow_derivative
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T04:39:16.594225+00:00
-- url     : https://prove2.me/theorems/5665db91-b31f-4d0d-a080-0213e42c396b
-- title:
--   Uniform differential and Lipschitz bounds for the mixed section flow
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
--   On $\|Z\|\le b_0/2$, the map
--   $H_t:Z\mapsto(\log n_t,Z_t)$ is differentiable, with
--   $\|DH_t\|\le e^{1/4}$ and $\|H_t(Z)-H_t(W)\|\le e^{1/4}\|Z-W\|$
--   for any two points of the ball.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/RestartSectionVariation.lean#L95-L122

import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_SectionRestartData
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

noncomputable section
open BianchiIX
open Set

theorem BianchiIX.exists_restartSectionMixedFlow_derivative :
    ∃ C ≥ (32 : ℝ), ∀ (h b T : ℝ),
      0 < h → C * h ≤ 1 / 4 → (0 < b ∧ b ≤ 1 / 16) → 0 ≤ T → C * b * T ≤ 1 / 8 →
      ∀ t ∈ Icc (0 : ℝ) T,
        (∀ Z : RestartCenterState, ‖Z‖ ≤ b / 2 →
          DifferentiableAt ℝ (restartSectionMixedFlow h t) Z ∧
          ‖fderiv ℝ (restartSectionMixedFlow h t) Z‖ ≤ Real.exp (1 / 4)) ∧
        (∀ Z W : RestartCenterState, ‖Z‖ ≤ b / 2 → ‖W‖ ≤ b / 2 →
          ‖restartSectionMixedFlow h t Z - restartSectionMixedFlow h t W‖ ≤ Real.exp (1 / 4) * ‖Z - W‖) := by sorry
