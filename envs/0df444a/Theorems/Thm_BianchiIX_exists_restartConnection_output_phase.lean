-- Prove2me | Theorems.Thm_BianchiIX_exists_restartConnection_output_phase
-- name    : BianchiIX.exists_restartConnection_output_phase
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T04:49:26.512441+00:00
-- url     : https://prove2.me/theorems/1deb6caa-d230-42b2-8ad2-5414df215393
-- title:
--   A positive radial slope for the phase after the angular connection
-- statement:
--   Write $\Phi_t x$ for the normalized vacuum Bianchi IX flow and
--   $x_h(Z)$ for the constraint-one, negative-first-shear chart with primary
--   wall $h$ and center coordinates $Z=(v,b,c)$ (second shear and the other
--   two walls). At time $t$, denote its primary wall by $n_t$ and center by
--   $Z_t$. Set $r(Z)=\sqrt{v^2+(b-c)^2}$. For $u=\sqrt{1-h^2}$ define
--   $A=3/(2+u)$, $B=3\sqrt3 h/(2+u)^2$, $H=9(1+u)/(2(2+u)^2)$,
--   $Q_h(v,w)=(Av+Bw)^2+H^2w^2$ and $F_h(Z)=\sqrt{Q_h(v,b-c)}/\sqrt3$.
--   On an angular annulus let $0<r$, $r\le\rho\le2r$,
--   $L\ge0$, $|\theta|\le L$, $M=8(L+1)$, $Z=(\theta\rho,\rho,\zeta)$
--   and $s=(q/2)\log(1/r)$. Write $Y=\Pi\Phi_s x_h(Z)$ for the fast
--   projective entry, $k=\sqrt{(Y_0-1)^2+Y_2^2}$, and $F=F_h(Z)$.
--   Primes mean ordinary derivatives in $\rho$ with the labels and cutoff
--   fixed. In each small-scale assertion $h>0$ is sufficiently small, and
--   then the scale $r>0$ is sufficiently small for the stated parameters.
--   At the partial core's downward unit hit, let $p$ be
--   the three exit parameters, $G$ the reflected core state after its
--   connection, and $t_R$ the absolute arrival time on the original orbit.
--   Write $g=G_0$ and $X=2/g$. The physical endpoint identity says that
--   the ascending unit entry with core $G$ equals the reflection of the
--   projective state of this orbit at $t_R$.
--   There is $C>0$ before $q>3$, $P>4$.
--   For $0<\zeta\le r^P$, the first positive unit hit from $Y$ has a
--   local $C^2$ time function selecting that first hit for nearby data.
--   The ensuing connection is valid and ends on the original physical
--   orbit. $X$ is differentiable with $|X-F|\le Cr^2$,
--   $|X'-F'|\le Cr$, $1/(8\sqrt3)\le X'\le C$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/RestartOutputPhase.lean#L12-L159

import Definitions.Def_BianchiIX_Analysis_CoreGrowthBudget
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_SectionRestartData
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_Linearization
import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreWeightedVariation
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreFlowVariation
import Definitions.Def_BianchiIX_Dynamics_ConnectionClock
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_Dynamics_ConnectionRegion
import Definitions.Def_BianchiIX_Dynamics_ConnectionExistence
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_Dynamics_ConnectionEvents
import Definitions.Def_BianchiIX_Dynamics_CoreExitEvents
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturn
import Definitions.Def_BianchiIX_Dynamics_CoreMultipliers
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturnValues
import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_Dynamics_ConnectionPhysicalReturn
import Definitions.Def_BianchiIX_Dynamics_CoreConnectionChart
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

theorem BianchiIX.exists_restartConnection_output_phase :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∃ C : ℝ, 0 < C ∧ ∀ q P : ℝ, 3 < q → 4 < P →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 < ζ ∧ ζ ≤ r ^ P) → ∀ ρ ∈ Icc r (2 * r),
            let s := q / 2 * Real.log (1 / r)
            let Y := restartFastProjectiveEntry h s θ ζ
            let F := fun a => restartReferenceRadialPhase h (restartRadialCurve θ ζ a)
            ∃ T > 0, IsLeast {t | 0 < t ∧ projectiveOriginalFlow (Y ρ) 0 t 2 = 1} T ∧
              ∃ τ : ProjectiveState → ℝ, τ (Y ρ) = T ∧ ContDiffAt ℝ 2 τ (Y ρ) ∧
                (∀ᶠ y in 𝓝 (Y ρ), IsLeast {t | 0 < t ∧
                  t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧ projectiveOriginalFlow y 0 t 2 = 1} (τ y)) ∧
                let out := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a))
                let f := fun a => coreRadius (out a 0) (out a 2)
                let p := fun a => coreExitConnectionParameters ![f a, out a 1, out a 3]
                let xr := fun a => 2 / connectionReturnPhysicalState (p a) 0
                connectionReturnValid (p ρ) ∧ connectionReturnState (p ρ) = toProjectiveState
                  (normalizedMaxCurve (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0
                    (s + T + connectionReturnTime (p ρ))) ∧
                DifferentiableAt ℝ xr ρ ∧ |xr ρ - F ρ| ≤ C * r ^ 2 ∧
                |deriv xr ρ - deriv F ρ| ≤ C * r ∧
                1 / (8 * Real.sqrt 3) ≤ deriv xr ρ ∧ deriv xr ρ ≤ C := by sorry
