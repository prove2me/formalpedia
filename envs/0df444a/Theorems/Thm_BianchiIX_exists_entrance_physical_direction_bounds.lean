-- Prove2me | Theorems.Thm_BianchiIX_exists_entrance_physical_direction_bounds
-- name    : BianchiIX.exists_entrance_physical_direction_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T04:42:34.646998+00:00
-- url     : https://prove2.me/theorems/c74061e4-1584-493a-862b-d9948f49cd56
-- title:
--   Differential of the arrival radius relative to the stable radius
-- statement:
--   In projective coordinates $y=(m,u,v,w)$ put
--   $k(y)=\sqrt{(m-1)^2+v^2}$. Write $Z(y)$ for the state at the
--   first positive unit entrance and $\kappa(y)=k(Z(y))$.
--   There exist $C>0$, $0<\epsilon\le10^{-4}$ such that
--   for $k\ge7/4$, $m\ge2$, $0<u,w\le\epsilon$, $0<v<1$, putting
--   $H=uv+v^2(u+w)^2$ and writing $k_s$ for the stable entrance radius,
--   $\kappa$ is $C^2$ at $y$ and $|\kappa-k_s|\le CH/k$. For $D\ge0$
--   and a direction $d$ with $|Dk_s[d]|\le Dk^2$ and
--   $|d_i|\le D k y_i$ for $i=1,2,3$,
--   $|D\kappa[d]-Dk_s[d]|\le CDkH$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/EntrancePhysicalDirections.lean#L72-L125

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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open BianchiIX
open Filter
open scoped Topology

theorem BianchiIX.exists_entrance_physical_direction_bounds :
    ∃ C > (0 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧
      ∀ y : ProjectiveState,
      let k := coreRadius (y 0) (y 2)
      let R := fun p : ProjectiveState => coreRadius (entranceReturnState p 0) (entranceReturnState p 2)
      let H := y 1 * y 2 + (y 2) ^ 2 * (y 1 + y 3) ^ 2
      7 / 4 ≤ k → 2 ≤ y 0 → (0 < y 1 ∧ y 1 ≤ ε) → (0 < y 2 ∧ y 2 < 1) →
      (0 < y 3 ∧ y 3 ≤ ε) →
      ContDiffAt ℝ 2 R y ∧ |R y - entranceStableRadius y| ≤ C * H / k ∧
      ∀ (D : ℝ) (d : ProjectiveState), 0 ≤ D →
        |fderiv ℝ entranceStableRadius y d| ≤ D * k ^ 2 →
        (∀ i : Fin 4, i ≠ 0 → |d i| ≤ D * k * y i) →
        |fderiv ℝ R y d - fderiv ℝ entranceStableRadius y d| ≤ C * D * k * H := by sorry
