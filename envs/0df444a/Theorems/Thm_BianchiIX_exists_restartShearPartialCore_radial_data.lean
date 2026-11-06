-- Prove2me | Theorems.Thm_BianchiIX_exists_restartShearPartialCore_radial_data
-- name    : BianchiIX.exists_restartShearPartialCore_radial_data
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T04:51:13.984571+00:00
-- url     : https://prove2.me/theorems/c2add701-aaf4-4f73-b642-c95b3ae9530f
-- title:
--   Shear entry data up to and including the incoming unit wall
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
--   For universal $K\ge1$ and sufficiently small $h$,
--   assume $Y_2\ge1$. The initial radicand and cutoff height are positive;
--   $a\le1$, $s\ge0$ exists. $Y$ is differentiable in the core region,
--   $k\ge6$, and either $Y_2>1$ or $Y_2=1$ with $Y_0\ge1$. The angle
--   $z\le0$ and $Y_1+Y_2Y_3\le1/k$. One has $2/(Ka)\le k\le K/a$,
--   $1/(4096a^2)\le-k'\le K/a^2$, $|z'|\le K/a$. The derivatives of
--   $Y_1,Y_2Y_3$ have absolute value at most $K/a$ times the respective
--   amplitudes.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/ShearRestartPartialCoreRadialData.lean#L10-L91

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_SectionRestartData
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_ShearTransportData
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
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
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section
open BianchiIX
open Set

theorem BianchiIX.exists_restartShearPartialCore_radial_data :
    ∃ hstar > (0 : ℝ), ∃ K ≥ (1 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            let Y := restartFastShearProjectiveEntry h s 1 n₂ n₃
            let k := restartFastShearCoreRadius h s 1 n₂ n₃
            let z := restartFastShearCoreAngle h s 1 n₂ n₃
            1 ≤ Y ρ 2 →
            a ≤ 1 ∧ 0 ≤ s ∧ 0 < restartSectionRadicand h (restartShearCurve 1 n₂ n₃ ρ) ∧
            s ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)) 0 ∧
            0 < restartFastShearHeight h s 1 n₂ n₃ ρ ∧ DifferentiableAt ℝ Y ρ ∧
            6 ≤ k ρ ∧ coreRegion (k ρ) (Y ρ) ∧
            (1 < Y ρ 2 ∨ (Y ρ 2 = 1 ∧ 1 ≤ Y ρ 0)) ∧ z ρ ≤ 0 ∧
            Y ρ 1 + Y ρ 2 * Y ρ 3 ≤ 1 / k ρ ∧
            2 / (K * a) ≤ k ρ ∧ k ρ ≤ K / a ∧ |deriv k ρ| ≤ K / a ^ 2 ∧
            1 / (4096 * a ^ 2) ≤ -deriv k ρ ∧
            |deriv (fun r => Y r 1) ρ| ≤ K * Y ρ 1 / a ∧
            |deriv (fun r => Y r 2 * Y r 3) ρ| ≤ K * (Y ρ 2 * Y ρ 3) / a ∧
            |deriv z ρ| ≤ K / a := by sorry
