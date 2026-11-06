-- Prove2me | Theorems.Thm_BianchiIX_exists_restartShearTail_connection_curve
-- name    : BianchiIX.exists_restartShearTail_connection_curve
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T05:03:12.306177+00:00
-- url     : https://prove2.me/theorems/ccb126d5-2e95-47fb-ac90-4dedfdc2ae8c
-- title:
--   Radius slopes, square-root cone and reciprocal phases through the long-tail connection
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
--   The long cutoff adds $S=(D/a)\log(1/a)$ to $s$.
--   Write $Y_L=\Pi\Phi_{s+S}x_h(Z)$, and write $(\zeta,\nu)=(n_2,n_3)$.
--   Take $0\le\epsilon\le1/128$, $0<\zeta,\nu\le2\epsilon a$,
--   $\zeta\le a^P$, $P>6D+2$.
--   At the partial core's downward unit hit, let $p$ be
--   the three exit parameters, $G$ the reflected core state after its
--   connection, and $t_R$ the absolute arrival time on the original orbit.
--   Write $g=G_0$ and $X=2/g$. The physical endpoint identity says that
--   the ascending unit entry with core $G$ equals the reflection of the
--   projective state of this orbit at $t_R$.
--   Take $q>3$, $D>4$ and the cutoff $s+S$.
--   For the downward radius $f$, $f>1$, $g>0$, $f',g'<0$,
--   $|g'/f'-1|\le1/(4p_0)$ and $3/4\le g'/f'\le5/4$.
--   Both reciprocal phases have positive derivatives and
--   $$2/g-2/f=-2(g-f)/(fg),\qquad (2/g)'/(2/f)'=(f/g)^2g'/f'.$$
--   The return $G$ is $C^2$ in $\rho$, $g'<0$, and
--   $|G_i'|\le\sqrt{G_i}\,|g'|$ for $i=1,2$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/ShearRestartTailConnectionCurve.lean#L11-L89

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_SectionRestartData
import Definitions.Def_BianchiIX_ShearTransportData
import Definitions.Def_BianchiIX_Dynamics_ConnectionExistence
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturn
import Definitions.Def_BianchiIX_Dynamics_EntranceReturn
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_Dynamics_ConnectionPhysicalReturn
import Definitions.Def_BianchiIX_Dynamics_CoreConnectionChart
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
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
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Module
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
open BianchiIX
open Set

theorem BianchiIX.exists_restartShearTail_connection_curve :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 128) →
          (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
          (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
          let s := shearTailTime a D + q / 2 * Real.log (1 / a)
          let Y := restartShearTailProjectiveEntry h a q ζ ν (shearTailTime a D)
          let f := fun r => partialCoreDownwardReturnState (Y r) 0
          let p := restartShearReturnParameters h s ζ ν
          let G := restartShearReturnState h s ζ ν
          let g := fun r => G r 0
          ContDiffAt ℝ 2 G ρ ∧ DifferentiableAt ℝ f ρ ∧
          1 < f ρ ∧ 0 < g ρ ∧ deriv f ρ < 0 ∧ deriv g ρ < 0 ∧
          |deriv g ρ / deriv f ρ - 1| ≤ 1 / (4 * p ρ 0) ∧
          (3 / 4 ≤ deriv g ρ / deriv f ρ ∧ deriv g ρ / deriv f ρ ≤ 5 / 4) ∧
          (∀ i : Fin 2, |deriv (fun r => G r i.succ) ρ| ≤ Real.sqrt (G ρ i.succ) * |deriv g ρ|) ∧
          DifferentiableAt ℝ (fun r => 2 / f r) ρ ∧ DifferentiableAt ℝ (fun r => 2 / g r) ρ ∧
          (0 < deriv (fun r => 2 / f r) ρ ∧ 0 < deriv (fun r => 2 / g r) ρ) ∧
          2 / g ρ - 2 / f ρ = -2 * (g ρ - f ρ) / (f ρ * g ρ) ∧
          deriv (fun r => 2 / g r) ρ / deriv (fun r => 2 / f r) ρ =
            (f ρ / g ρ) ^ 2 * (deriv g ρ / deriv f ρ) := by sorry
