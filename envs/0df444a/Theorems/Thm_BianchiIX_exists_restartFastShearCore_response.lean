-- Prove2me | Theorems.Thm_BianchiIX_exists_restartFastShearCore_response
-- name    : BianchiIX.exists_restartFastShearCore_response
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T04:48:58.749192+00:00
-- url     : https://prove2.me/theorems/137b06f1-730c-44c2-bfbc-3daed75903f4
-- title:
--   The fast shear entry has a decreasing radius and controlled angular derivative
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
--   There are $h_*,K>0$ such that for $0<h\le h_*$,
--   $q,P>2$, $0\le\epsilon\le1/64$, $0\le n_i\le2\epsilon a$,
--   $n_3\le a^P$, the cutoff exists. The radius is differentiable,
--   $k\ge6$, $1/(16a)\le k\le32/a$ and
--   $1/(4096a^2)\le-k'\le1536/a^2$. If $Y_2>0$ the angle is differentiable
--   and its radial derivative has absolute value at most $K/a$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/ShearRestartCoreResponse.lean#L41-L111

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_SectionRestartData
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
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
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section
open BianchiIX
open Set

theorem BianchiIX.exists_restartFastShearCore_response :
    ∃ hstar > (0 : ℝ), ∃ K > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 2 < q → 2 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let T := q / 2 * Real.log (1 / a)
            let k := restartFastShearCoreRadius h T 1 n₂ n₃
            let z := restartFastShearCoreAngle h T 1 n₂ n₃
            T ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)) 0 ∧
            DifferentiableAt ℝ k ρ ∧ 6 ≤ k ρ ∧ 1 / (16 * a) ≤ k ρ ∧ k ρ ≤ 32 / a ∧
            1 / (4096 * a ^ 2) ≤ -deriv k ρ ∧ -deriv k ρ ≤ 1536 / a ^ 2 ∧
            (0 < restartFastShearProjectiveEntry h T 1 n₂ n₃ ρ 2 →
              DifferentiableAt ℝ z ρ ∧ |deriv z ρ| ≤ K / a) := by sorry
