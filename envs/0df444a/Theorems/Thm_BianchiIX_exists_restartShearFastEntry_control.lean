-- Prove2me | Theorems.Thm_BianchiIX_exists_restartShearFastEntry_control
-- name    : BianchiIX.exists_restartShearFastEntry_control
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T04:43:20.187467+00:00
-- url     : https://prove2.me/theorems/09df737c-16d8-4bd1-a22c-d9c753c8fc4f
-- title:
--   Control of signed shear data and wall-relative derivatives at the fast cutoff
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
--   There exist $C\ge32$, $h_*>0$ such that for $0<h\le h_*$,
--   $q>2$, $0\le\epsilon\le1/64$ and $0\le n_i\le2\epsilon a$ both signed
--   families reach the cutoff on constraint one with positive chart radicand,
--   first shear at most $-15/16$, $a\le1$, $8a\le1/16$, $s\ge0$. The
--   strong wall is in $(0,ha^q]$, $\|Z_s\|\le8a$ and
--   $3a/4\le\omega(Z_s)_0\le9a/4$. The radial tangent is the section
--   differential in direction $(\omega,0,0)$, has norm at most two, and
--   $|n_s'|\le2n_s/a$. Each weak amplitude $w$ stays in $[w(0)/2,2w(0)]$
--   and $|w'|\le8Cw/a$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/ShearRestartFastEntry.lean#L11-L93

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_SectionRestartData
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
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

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

theorem BianchiIX.exists_restartShearFastEntry_control :
    ∃ C ≥ (32 : ℝ), ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q : ℝ, 2 < q → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε σ n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) → |σ| = 1 →
          (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let T := q / 2 * Real.log (1 / a)
            let Z := restartShearCurve σ n₂ n₃ ρ
            let x := normalizedMaxCurve (restartSectionChart h Z) 0 T
            let p := restartSectionRadialState h T Z
            let v := fderiv ℝ (restartSectionRadialState h T) Z (restartShearDirection σ)
            a ≤ 1 ∧ 8 * a ≤ 1 / 16 ∧ 0 ≤ T ∧ 0 < restartSectionRadicand h Z ∧
            T ∈ normalizedMaxDomain (restartSectionChart h Z) 0 ∧ stateConstraint x = 1 ∧ x 0 ≤ -(15 / 16) ∧
            HasDerivAt (fun y => restartSectionRadialState h T (restartShearCurve σ n₂ n₃ y)) v ρ ∧
            0 < p.1 ∧ p.1 ≤ h * a ^ q ∧
            (3 * a / 4 ≤ σ * p.2 0 ∧ σ * p.2 0 ≤ 9 * a / 4) ∧ ‖p.2‖ ≤ 8 * a ∧
            ‖v‖ ≤ 2 ∧ |v.1| ≤ 2 * p.1 / a ∧
            ∀ i : Fin 2, Z i.succ / 2 ≤ p.2 i.succ ∧ p.2 i.succ ≤ 2 * Z i.succ ∧
              |v.2 i.succ| ≤ 8 * C * p.2 i.succ / a := by sorry
