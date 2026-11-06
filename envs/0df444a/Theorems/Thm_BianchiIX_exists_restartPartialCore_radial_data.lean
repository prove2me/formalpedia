-- Prove2me | Theorems.Thm_BianchiIX_exists_restartPartialCore_radial_data
-- name    : BianchiIX.exists_restartPartialCore_radial_data
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T04:47:06.249222+00:00
-- url     : https://prove2.me/theorems/45cd8e4a-ed15-4351-93bb-ab08f6389d21
-- title:
--   Angular restart data at entry to a partial core
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
--   Choose constants $K\ge1$, $D>0$ before $q>3$,
--   $P>4$; take $0\le\zeta\le r^P$. The chart radicand and cutoff
--   height are positive, $r\le1$, $s\ge0$ exists. $Y$ is differentiable
--   and in the core region, $Y_2>1$, $Y_1+Y_2Y_3\le1/k$.
--   With $A=\operatorname{arsinh}(4M)$ its core angle $z$ satisfies
--   $z\le A$, $k\ge\max(6,2\cosh A)$, $2/(Kr)\le k\le K/r$,
--   $1/(Dr^2)\le-k'\le K/r^2$, $|z'|\le K/r$. The radial derivatives
--   of $Y_1$ and $Y_2Y_3$ are bounded by $K/r$ times the respective
--   amplitudes.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/RestartPartialCoreRadialData.lean#L10-L104

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_SectionRestartData
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
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
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

noncomputable section
open BianchiIX
open Set

theorem BianchiIX.exists_restartPartialCore_radial_data :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∃ K : ℝ, 1 ≤ K ∧ ∃ D : ℝ, 0 < D ∧
        ∀ q P : ℝ, 3 < q → 4 < P →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 ≤ ζ ∧ ζ ≤ r ^ P) → ∀ ρ ∈ Icc r (2 * r),
            let s := q / 2 * Real.log (1 / r)
            let Y := restartFastProjectiveEntry h s θ ζ
            let k := restartFastCoreRadius h s θ ζ
            let z := restartFastCoreAngle h s θ ζ
            let Z := Real.arsinh (4 * (8 * (L + 1)))
            r ≤ 1 ∧ 0 ≤ s ∧ 0 < restartSectionRadicand h (restartRadialCurve θ ζ ρ) ∧
            s ∈ normalizedMaxDomain (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 ∧
            0 < restartFastProjectionHeight h s θ ζ ρ ∧ DifferentiableAt ℝ Y ρ ∧
            0 ≤ Z ∧ max 6 (2 * Real.cosh Z) ≤ k ρ ∧ z ρ ≤ Z ∧
            coreRegion (k ρ) (Y ρ) ∧ 1 < Y ρ 2 ∧ Y ρ 1 + Y ρ 2 * Y ρ 3 ≤ 1 / k ρ ∧
            2 / (K * r) ≤ k ρ ∧ k ρ ≤ K / r ∧ |deriv k ρ| ≤ K / r ^ 2 ∧
            1 / (D * r ^ 2) ≤ -deriv k ρ ∧
            |deriv (fun a => Y a 1) ρ| ≤ K * Y ρ 1 / r ∧
            |deriv (fun a => Y a 2 * Y a 3) ρ| ≤ K * (Y ρ 2 * Y ρ 3) / r ∧
            |deriv z ρ| ≤ K / r := by sorry
