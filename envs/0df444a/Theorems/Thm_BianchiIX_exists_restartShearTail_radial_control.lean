-- Prove2me | Theorems.Thm_BianchiIX_exists_restartShearTail_radial_control
-- name    : BianchiIX.exists_restartShearTail_radial_control
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T04:49:09.446926+00:00
-- url     : https://prove2.me/theorems/a66ce4a0-a548-426d-9dda-28581c546f7b
-- title:
--   Energy moments and radial variations throughout a long shear tail
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
--   For $q>2$, $D\ge0$ and universal $C\ge32$, write
--   $v(t)=\partial_\rho\Phi_{s+t}x_h(Z)$ and $L(t)=\max_i|\partial_\rho
--   N_i/N_i|$. For $E=\sum_i N_i^2+N_1(N_2+N_3)$ let
--   $J_j=\int_0^S t^j E\,dt$. One has $a\le1/256$, $S\ge0$,
--   $L(0)\le2+4Cq|\log a|$, $J_0\le4a$, $J_1\le1/256+(2+D)a$,
--   $9J_0\le\log2$, $2J_0+16J_1\le1/2$, $L(0)J_0\le1/16$.
--   At every $t\in[0,S]$ the stated derivative exists, the walls are
--   positive, $|v_1(t)|\le5$ and $L(t)\le2L(0)+20t$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/ShearRestartTailRadial.lean#L12-L116

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_SectionRestartData
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_Linearization
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_FlowTransport
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

noncomputable section
open BianchiIX
open Set MeasureTheory

theorem BianchiIX.exists_restartShearTail_radial_control :
    ∃ C ≥ (32 : ℝ), ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 2 < q → 0 ≤ D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε ζ ν : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 128) →
            (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
            (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let T := shearTailTime a D
            let α := fun t => restartShearTailFlow h a q ζ ν t ρ
            let v := fun t => restartShearTailRadialVariation h a q ζ ν t ρ
            let L₀ := shearTailLogSize (α 0) (v 0)
            let J₀ := ∫ t in 0..T, shearTailEnergy (α t)
            let J₁ := ∫ t in 0..T, t * shearTailEnergy (α t)
            a ≤ 1 / 256 ∧ 0 ≤ T ∧ L₀ ≤ 2 + 4 * C * q * |Real.log a| ∧
            J₀ ≤ 4 * a ∧ J₁ ≤ 1 / 256 + (2 + D) * a ∧
            9 * J₀ ≤ Real.log 2 ∧ 2 * J₀ + 16 * J₁ ≤ 1 / 2 ∧ L₀ * J₀ ≤ 1 / 16 ∧
            ∀ t ∈ Icc (0 : ℝ) T,
              HasDerivAt (restartShearTailFlow h a q ζ ν t) (v t) ρ ∧ positiveWalls (α t) ∧
              |v t 1| ≤ 5 ∧ shearTailLogSize (α t) (v t) ≤ 2 * L₀ + 20 * t ∧
              shearTailLogSize (α t) (v t) ≤ 4 + 8 * C * q * |Real.log a| + 20 * t := by sorry
