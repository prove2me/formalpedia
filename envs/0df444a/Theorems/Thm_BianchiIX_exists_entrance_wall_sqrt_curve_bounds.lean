-- Prove2me | Theorems.Thm_BianchiIX_exists_entrance_wall_sqrt_curve_bounds
-- name    : BianchiIX.exists_entrance_wall_sqrt_curve_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T04:42:07.893035+00:00
-- url     : https://prove2.me/theorems/1baf73c6-db0b-46ed-9b5b-17f3f910a1be
-- title:
--   Square-root bounds for wall derivatives at a physical entrance
-- statement:
--   In projective coordinates $y=(m,u,v,w)$ put
--   $k(y)=\sqrt{(m-1)^2+v^2}$. Write $Z(y)$ for the state at the
--   first positive unit entrance and $\kappa(y)=k(Z(y))$.
--   There are $C>0$ and $0<\epsilon\le10^{-4}$.
--   Let $y=Y(\rho)$ on a differentiable curve at $\rho$, with $k=k(y)\ge7/4$,
--   $m\ge1$, $0<u,w\le\epsilon$, $0<v<1$. For $D\ge0$ assume
--   $|m'|\le Dk^2$ and $|Y_i'|\le DkY_i$ for $i=1,2,3$.
--   The arrival map along the curve is differentiable,
--   $Z_1,Z_3>0$, $|Z_1'|\le CDk^2\sqrt{uv}\sqrt{Z_1}$ and
--   $|Z_3'|\le CDk\sqrt{wv}\sqrt{Z_3}$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/EntranceWallCone.lean#L36-L61

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Definitions.Def_BianchiIX_Analysis_SignedRowGrowth
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ProjectiveClock
import Definitions.Def_BianchiIX_Dynamics_Linearization
import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_EntranceRegion
import Definitions.Def_BianchiIX_Dynamics_EntranceReturn
import Definitions.Def_BianchiIX_EntrancePhaseResponseData
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
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

noncomputable section
open BianchiIX

theorem BianchiIX.exists_entrance_wall_sqrt_curve_bounds :
    ∃ C > (0 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧
      ∀ (Y : ℝ → ProjectiveState) (ρ D : ℝ),
      let y := Y ρ
      let k := coreRadius (y 0) (y 2)
      let Z := fun t => entranceReturnState (Y t)
      DifferentiableAt ℝ Y ρ → 0 ≤ D → 7 / 4 ≤ k → 1 ≤ y 0 →
      (0 < y 1 ∧ y 1 ≤ ε) → (0 < y 2 ∧ y 2 < 1) → (0 < y 3 ∧ y 3 ≤ ε) →
      |deriv (fun t => Y t 0) ρ| ≤ D * k ^ 2 →
      (∀ i : Fin 4, i ≠ 0 → |deriv (fun t => Y t i) ρ| ≤ D * k * y i) →
      DifferentiableAt ℝ Z ρ ∧ 0 < Z ρ 1 ∧ 0 < Z ρ 3 ∧
      |deriv (fun t => Z t 1) ρ| ≤ C * D * k ^ 2 * Real.sqrt (y 1 * y 2) * Real.sqrt (Z ρ 1) ∧
      |deriv (fun t => Z t 3) ρ| ≤ C * D * k * Real.sqrt (y 3 * y 2) * Real.sqrt (Z ρ 3) := by sorry
