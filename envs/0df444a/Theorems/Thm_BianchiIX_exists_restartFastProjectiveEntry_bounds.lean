-- Prove2me | Theorems.Thm_BianchiIX_exists_restartFastProjectiveEntry_bounds
-- name    : BianchiIX.exists_restartFastProjectiveEntry_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T04:43:23.920307+00:00
-- url     : https://prove2.me/theorems/f0a93444-cec5-44f6-83ff-3475285e8c87
-- title:
--   Projective coordinates of the angular restart at the fast cutoff
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
--   For $q>2$, $0\le\zeta\le r^2$, the cutoff exists.
--   Its projective entry, core angle and height $H=1+(\Phi_s x)_0$ are
--   differentiable, $r^2/16\le H\le10(Mr)^2$ and
--   $|H'|\le64M(L+1)r$. The active wall lies between
--   $\max(2,1/(20M^2r))$ and $32M/r$, $0<Y_1\le32h r^{q-2}$,
--   $0\le Y_3\le64\zeta/r^2$, $0\le Y_2Y_3\le2048M\zeta/r^3$
--   and the absolute core angle is at most $\operatorname{arsinh}(4M)$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/RestartFastProjectiveEntry.lean#L41-L116

import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_SectionRestartData
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
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.Deriv.Pi

noncomputable section
open BianchiIX
open Set

theorem BianchiIX.exists_restartFastProjectiveEntry_bounds :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∀ q : ℝ, 2 < q → ∃ rstar : ℝ, 0 < rstar ∧
        ∀ r ∈ Ioc (0 : ℝ) rstar, ∀ θ ζ : ℝ, |θ| ≤ L → (0 ≤ ζ ∧ ζ ≤ r ^ 2) →
          ∀ ρ ∈ Icc r (2 * r),
            let T := q / 2 * Real.log (1 / r)
            let M := 8 * (L + 1)
            let y := restartFastProjectiveEntry h T θ ζ ρ
            T ∈ normalizedMaxDomain (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 ∧
            DifferentiableAt ℝ (restartFastProjectiveEntry h T θ ζ) ρ ∧
            DifferentiableAt ℝ (restartFastCoreAngle h T θ ζ) ρ ∧
            DifferentiableAt ℝ (restartFastProjectionHeight h T θ ζ) ρ ∧
            r ^ 2 / 16 ≤ restartFastProjectionHeight h T θ ζ ρ ∧
            restartFastProjectionHeight h T θ ζ ρ ≤ 10 * (M * r) ^ 2 ∧
            |deriv (restartFastProjectionHeight h T θ ζ) ρ| ≤ 64 * M * (L + 1) * r ∧
            2 ≤ y 2 ∧ 1 / (20 * M ^ 2 * r) ≤ y 2 ∧ y 2 ≤ 32 * M / r ∧
            (0 < y 1 ∧ y 1 ≤ 32 * h * r ^ (q - 2)) ∧
            (0 ≤ y 3 ∧ y 3 ≤ 64 * ζ / r ^ 2) ∧
            (0 ≤ y 2 * y 3 ∧ y 2 * y 3 ≤ 2048 * M * ζ / r ^ 3) ∧
            |restartFastCoreAngle h T θ ζ ρ| ≤ Real.arsinh (4 * M) := by sorry
