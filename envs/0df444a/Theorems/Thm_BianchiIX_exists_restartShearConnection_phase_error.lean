-- Prove2me | Theorems.Thm_BianchiIX_exists_restartShearConnection_phase_error
-- name    : BianchiIX.exists_restartShearConnection_phase_error
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T04:53:35.458578+00:00
-- url     : https://prove2.me/theorems/2461c772-e2e2-4f2c-8b6d-d66e8a83eef3
-- title:
--   Amplitude-sensitive phase error through the shear connection
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
--   Take $q>3$, $P>4$, $0\le\epsilon\le1/64$,
--   $0\le n_2,n_3\le2\epsilon a$ and $n_3\le a^P$.
--   At the partial core's downward unit hit, let $p$ be
--   the three exit parameters, $G$ the reflected core state after its
--   connection, and $t_R$ the absolute arrival time on the original orbit.
--   Write $g=G_0$ and $X=2/g$. The physical endpoint identity says that
--   the ascending unit entry with core $G$ equals the reflection of the
--   projective state of this orbit at $t_R$.
--   There are uniform $K\ge1$, $C>0$. Assume
--   $n_3>0$ and $Y_2\ge1$. The downward return is the first unit hit
--   after $s$; the connection is valid and ends on the original orbit.
--   Put $U=Y_1$, $W=Y_2Y_3$, and let $f$ be the downward exit radius.
--   Then $a\le1$, $k\ge6$, $2/(Ka)\le k\le K/a$, $g\ge k/4$,
--   $U>0$, $0<W\le1$, $U+W\le Ka$. The radius, exit radius, connection
--   phase error $\Delta$ and output radius are differentiable. Writing
--   $R=2/g-2/(k-2)$, the uniform bounds include
--   $|f-k|\le16K(U+aW^2)$, $|(f-k)'|\lesssim(U+aW)/a^2$,
--   $|\Delta|\le Ca(U+W^2)$, $|\Delta'|\le C(U+W^2)$,
--   $|R|\lesssim a^2(U+aW^2)$ and $|R'|\lesssim U+aW$.
--   The implied constants depend only on the fixed variation bounds.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/ShearRestartConnectionPhase.lean#L11-L91

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Analysis_CoreGrowthBudget
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_SectionRestartData
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_Dynamics_ConnectionEvents
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturn
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturnValues
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_Dynamics_ConnectionPhysicalReturn
import Definitions.Def_BianchiIX_Dynamics_CoreConnectionChart
import Definitions.Def_BianchiIX_ShearTransportData
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
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Module
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
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
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section
open BianchiIX
open Set

theorem BianchiIX.exists_restartShearConnection_phase_error :
    ∃ hstar > (0 : ℝ), ∃ K ≥ (1 : ℝ), ∃ C > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            let Y := restartFastShearProjectiveEntry h s 1 n₂ n₃
            let k := restartFastShearCoreRadius h s 1 n₂ n₃
            let U := Y ρ 1
            let W := Y ρ 2 * Y ρ 3
            let T := partialCoreDownwardReturnTime (Y ρ)
            let out := fun b => projectiveOriginalFlow (Y b) 0 (partialCoreDownwardReturnTime (Y b))
            let f := fun b => coreRadius (out b 0) (out b 2)
            let p := fun b => coreExitConnectionParameters ![f b, out b 1, out b 3]
            let Δ := fun b => connectionReturnPhaseError (p b)
            let g := fun b => connectionReturnPhysicalState (p b) 0
            let E := 16 * K + 4 * (4096 * coreVariationBound) * K ^ 2 + C
            let R := fun b => 2 / g b - (2 / k b) / (1 - 2 / k b)
            1 ≤ Y ρ 2 →
            0 < T ∧ IsLeast {t | s < t ∧ toProjectiveState
              (normalizedMaxCurve (restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)) 0 t) 2 = 1} (s + T) ∧
            connectionReturnValid (p ρ) ∧ connectionReturnState (p ρ) = toProjectiveState
              (normalizedMaxCurve (restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)) 0
                (s + T + connectionReturnTime (p ρ))) ∧
            a ≤ 1 ∧ 6 ≤ k ρ ∧ 2 / (K * a) ≤ k ρ ∧ k ρ ≤ K / a ∧
            0 < U ∧ (0 < W ∧ W ≤ 1) ∧ U + W ≤ K * a ∧
            DifferentiableAt ℝ k ρ ∧ DifferentiableAt ℝ f ρ ∧
            |f ρ - k ρ| ≤ 16 * K * (U + a * W ^ 2) ∧
            |deriv (fun b => f b - k b) ρ| ≤ 4 * (4096 * coreVariationBound) * K ^ 2 * (U + a * W) / a ^ 2 ∧
            DifferentiableAt ℝ Δ ρ ∧ |Δ ρ| ≤ C * a * (U + W ^ 2) ∧ |deriv Δ ρ| ≤ C * (U + W ^ 2) ∧
            DifferentiableAt ℝ g ρ ∧ k ρ / 4 ≤ g ρ ∧
            DifferentiableAt ℝ R ρ ∧ |R ρ| ≤ 8 * E * K ^ 2 * a ^ 2 * (U + a * W ^ 2) ∧
            |deriv R ρ| ≤ (8 * E * K ^ 2 + 32 * E * K ^ 4) * (U + a * W) := by sorry
