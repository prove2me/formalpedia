-- Prove2me | Theorems.Thm_BianchiIX_exists_entrance_physical_curve_bounds
-- name    : BianchiIX.exists_entrance_physical_curve_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T04:42:59.052198+00:00
-- url     : https://prove2.me/theorems/196334c3-845d-4e26-8889-d153e325f284
-- title:
--   The radius at a physical entrance along a differentiable curve
-- statement:
--   In projective coordinates $y=(m,u,v,w)$ put
--   $k(y)=\sqrt{(m-1)^2+v^2}$. Write $Z(y)$ for the state at the
--   first positive unit entrance and $\kappa(y)=k(Z(y))$.
--   There are $C>0$ and $0<\epsilon\le10^{-4}$.
--   Let $y=Y(\rho)$ on a differentiable curve at $\rho$, with $k=k(y)\ge7/4$,
--   $m\ge1$, $0<u,w\le\epsilon$, $0<v<1$. For $D\ge0$ assume
--   $|m'|\le Dk^2$ and $|Y_i'|\le DkY_i$ for $i=1,2,3$.
--   Put $b=u+w$, $H=uv+v^2 b^2$. Both radii are
--   differentiable along the curve, and
--   $|\kappa-k|\le C(b^2+H)/k$, $|\kappa'-k'|\le CD(b^2+kH)$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/EntrancePhysicalRadialResponse.lean#L60-L89

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
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ProjectiveClock
import Definitions.Def_BianchiIX_Dynamics_Linearization
import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_EntranceRegion
import Definitions.Def_BianchiIX_Dynamics_EntranceReturn
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
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
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open BianchiIX

theorem BianchiIX.exists_entrance_physical_curve_bounds :
    ∃ C > (0 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧
      ∀ (Y : ℝ → ProjectiveState) (ρ D : ℝ),
      let y := Y ρ
      let k := coreRadius (y 0) (y 2)
      let κ := fun t => coreRadius (entranceReturnState (Y t) 0) (entranceReturnState (Y t) 2)
      let K := fun t => coreRadius (Y t 0) (Y t 2)
      let b := y 1 + y 3
      let H := y 1 * y 2 + (y 2) ^ 2 * b ^ 2
      DifferentiableAt ℝ Y ρ → 0 ≤ D → 7 / 4 ≤ k → 1 ≤ y 0 →
      (0 < y 1 ∧ y 1 ≤ ε) → (0 < y 2 ∧ y 2 < 1) → (0 < y 3 ∧ y 3 ≤ ε) →
      |deriv (fun t => Y t 0) ρ| ≤ D * k ^ 2 →
      (∀ i : Fin 4, i ≠ 0 → |deriv (fun t => Y t i) ρ| ≤ D * k * y i) →
      DifferentiableAt ℝ κ ρ ∧ DifferentiableAt ℝ K ρ ∧
      |κ ρ - k| ≤ C * (b ^ 2 + H) / k ∧ |deriv κ ρ - deriv K ρ| ≤ C * D * (b ^ 2 + k * H) := by sorry
