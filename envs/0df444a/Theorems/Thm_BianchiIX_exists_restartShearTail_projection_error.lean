-- Prove2me | Theorems.Thm_BianchiIX_exists_restartShearTail_projection_error
-- name    : BianchiIX.exists_restartShearTail_projection_error
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T04:51:21.555009+00:00
-- url     : https://prove2.me/theorems/b9bacb4b-eadd-4a3d-a8df-9534318a1ff1
-- title:
--   The projected phase differs from the physical tail phase by a quadratic error
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
--   For $q,D>2$ choose $K>0$ before $P$. At $s+S$, the
--   orbit exists with $1+x_0>0$. The growing-circle reciprocal phase minus
--   the physical radial phase is differentiable in $\rho$; its value has
--   absolute magnitude at most $Ka^2$ and its derivative at most $Ka$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/ShearRestartTailProjectionError.lean#L17-L93

import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_ShearTransportData
import Definitions.Def_BianchiIX_RadialTransportData
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
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

theorem BianchiIX.exists_restartShearTail_projection_error :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D : ℝ, 2 < q → 2 < D → ∃ K > (0 : ℝ),
        ∀ P : ℝ, 6 * D + 2 < P → ∃ astar > (0 : ℝ),
          ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
            (0 ≤ ε ∧ ε ≤ 1 / 128) →
            (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
            (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let T := shearTailTime a D
            let E := fun r => restartShearTailProjectionPhase h a q ζ ν T r -
              restartShearTailPhase h a q ζ ν T r
            T + q / 2 * Real.log (1 / a) ∈
              normalizedMaxDomain (restartSectionChart h (restartShearCurve 1 ζ ν ρ)) 0 ∧
            0 < 1 + restartShearTailFlow h a q ζ ν T ρ 0 ∧
            DifferentiableAt ℝ E ρ ∧ |E ρ| ≤ K * a ^ 2 ∧ |deriv E ρ| ≤ K * a := by sorry
