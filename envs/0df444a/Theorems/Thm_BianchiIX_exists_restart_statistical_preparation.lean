-- Prove2me | Theorems.Thm_BianchiIX_exists_restart_statistical_preparation
-- name    : BianchiIX.exists_restart_statistical_preparation
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T04:52:28.371906+00:00
-- url     : https://prove2.me/theorems/e0187b71-520e-46d5-896c-d9218e5f8e80
-- title:
--   Angular restarts give a measurable family of admissible era curves
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
--   For a returned phase $X=2/G_0$, the extended core
--   curve at radius $2/X$ agrees with the actual return $G$.
--   Admissibility at budget $B$ means that for every radius above two its
--   two wall functions are positive, of class $C^1$, have sum at most
--   $B$, and have derivative bounded in absolute value by their own
--   square root. For $q>3$, $P>4$ and any prescribed
--   $B_*>0$ take $r$ sufficiently small. On $0<\zeta\le r^P$ the budget
--   $B=6400M\zeta/r^3$ lies in $(0,B_*]$ and the extended curve is
--   admissible at $B$. The budget and state are jointly measurable on the
--   selected labels times $[r,2r]$. The phase $X$ is in $(0,1)$ and is
--   differentiable with $X'\ge1/(8\sqrt3)$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/RestartStatisticalPreparation.lean#L16-L99

import Definitions.Def_BianchiIX_Analysis_CoreGrowthBudget
import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreWeightedVariation
import Definitions.Def_BianchiIX_Dynamics_CoreFlowVariation
import Definitions.Def_BianchiIX_Dynamics_ProjectiveReflection
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_Dynamics_CoreExitEvents
import Definitions.Def_BianchiIX_Dynamics_CoreMultipliers
import Definitions.Def_BianchiIX_SectionRestartData
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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Order.Compact
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
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.List.Induction
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Floor.Semiring

noncomputable section
open BianchiIX
open Set

theorem BianchiIX.exists_restart_statistical_preparation :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ L : ℝ, 0 ≤ L →
      ∀ q P : ℝ, 3 < q → 4 < P → ∀ Bstar : ℝ, 0 < Bstar →
        ∃ rstar > (0 : ℝ), ∀ r ∈ Ioc (0 : ℝ) rstar,
          let s := q / 2 * Real.log (1 / r)
          Measurable (fun p : restartLabelSet L r P × Icc r (2 * r) =>
            (restartAmplitudeBudget L r p.1.val.2, restartReturnState h s p.1.val.1 p.1.val.2 p.2)) ∧
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 < ζ ∧ ζ ≤ r ^ P) →
            restartAmplitudeBudget L r ζ ∈ Ioc 0 Bstar ∧
            (restartEraCurve h s θ ζ r).Admissible (restartAmplitudeBudget L r ζ) ∧
            ∀ ρ ∈ Icc r (2 * r),
              restartReturnPhase h s θ ζ ρ ∈ Ioo 0 1 ∧
              DifferentiableAt ℝ (restartReturnPhase h s θ ζ) ρ ∧
              1 / (8 * Real.sqrt 3) ≤ deriv (restartReturnPhase h s θ ζ) ρ ∧
              (restartEraCurve h s θ ζ r).state (2 / restartReturnPhase h s θ ζ ρ) =
                restartReturnState h s θ ζ ρ := by sorry
