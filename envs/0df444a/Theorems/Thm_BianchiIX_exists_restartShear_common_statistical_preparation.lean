-- Prove2me | Theorems.Thm_BianchiIX_exists_restartShear_common_statistical_preparation
-- name    : BianchiIX.exists_restartShear_common_statistical_preparation
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T05:07:28.882133+00:00
-- url     : https://prove2.me/theorems/984f0dbe-2ca6-4600-bd3b-27060077a33b
-- title:
--   Shear restarts give admissible era curves for either small-wall ordering
-- statement:
--   Write $\Phi_t x$ for the normalized vacuum Bianchi IX flow and
--   $x_h(Z)$ for the constraint-one, negative-first-shear chart with primary
--   wall $h$ and center coordinates $Z=(v,b,c)$ (second shear and the other
--   two walls). At time $t$, denote its primary wall by $n_t$ and center by
--   $Z_t$. Set $r(Z)=\sqrt{v^2+(b-c)^2}$. For $u=\sqrt{1-h^2}$ define
--   $A=3/(2+u)$, $B=3\sqrt3 h/(2+u)^2$, $H=9(1+u)/(2(2+u)^2)$,
--   $Q_h(v,w)=(Av+Bw)^2+H^2w^2$ and $F_h(Z)=\sqrt{Q_h(v,b-c)}/\sqrt3$.
--   On a shear annulus take $0<a$, $\rho\in[a,2a]$,
--   $Z=(\rho,n_2,n_3)$, $s=(q/2)\log(1/a)$, $Y=\Pi\Phi_s x_h(Z)$,
--   $k=\sqrt{(Y_0-1)^2+Y_2^2}$ and $F=F_h(Z)$. A signed annulus uses
--   $Z=(\omega\rho,n_2,n_3)$, $|\omega|=1$. Here $h>0$ is sufficiently
--   small and $a>0$ is sufficiently small thereafter. Primes are ordinary
--   radial derivatives with labels and cutoff fixed.
--   Take $q>3$, $D>4$, $P>6D+2$,
--   $0\le\epsilon\le1/128$, $0<n_2,n_3\le2\epsilon a$ and
--   $\min(n_2,n_3)\le a^P$.
--   For a returned phase $X=2/G_0$, the extended core
--   curve at radius $2/X$ agrees with the actual return $G$.
--   Admissibility at budget $B$ means that for every radius above two its
--   two wall functions are positive, of class $C^1$, have sum at most
--   $B$, and have derivative bounded in absolute value by their own
--   square root. For any $B_*>0$, decrease $a$ before
--   choosing $\epsilon$ and the labels. The budget $B=800n_2n_3/a^4$
--   is in $(0,B_*]$ and the extended curve is admissible at $B$. The
--   budget and return state are jointly measurable on the selected labels
--   times $[a,2a]$. The phase $X\in(0,1)$ is differentiable and
--   $X'\ge1/(4\sqrt3)$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/ShearRestartCommonPreparation.lean#L27-L101

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_SectionRestartData
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Analysis_AmplitudeExtension
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveReflection
import Definitions.Def_BianchiIX_ShearTransportData
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturn
import Definitions.Def_BianchiIX_Dynamics_EntranceReturn
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
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
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
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

theorem BianchiIX.exists_restartShear_common_statistical_preparation :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P → ∀ Bstar : ℝ, 0 < Bstar →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 128) →
          let s := q / 2 * Real.log (1 / a)
          Measurable (fun p : restartShearCommonLabelSet ε a P × Icc a (2 * a) =>
            (restartShearAmplitudeBudget a p.1.val.1 p.1.val.2,
              restartShearReturnState h s p.1.val.1 p.1.val.2 p.2)) ∧
          ∀ n₂ n₃ : ℝ, (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
            min n₂ n₃ ≤ a ^ P →
            restartShearAmplitudeBudget a n₂ n₃ ∈ Ioc 0 Bstar ∧
            (restartShearEraCurve h s n₂ n₃ a).Admissible (restartShearAmplitudeBudget a n₂ n₃) ∧
            ∀ ρ ∈ Icc a (2 * a), restartShearReturnPhase h s n₂ n₃ ρ ∈ Ioo 0 1 ∧
              DifferentiableAt ℝ (restartShearReturnPhase h s n₂ n₃) ρ ∧
              1 / (4 * Real.sqrt 3) ≤ deriv (restartShearReturnPhase h s n₂ n₃) ρ ∧
              (restartShearEraCurve h s n₂ n₃ a).state (2 / restartShearReturnPhase h s n₂ n₃ ρ) =
                restartShearReturnState h s n₂ n₃ ρ := by sorry
