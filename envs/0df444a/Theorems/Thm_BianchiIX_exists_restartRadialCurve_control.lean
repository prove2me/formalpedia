-- Prove2me | Theorems.Thm_BianchiIX_exists_restartRadialCurve_control
-- name    : BianchiIX.exists_restartRadialCurve_control
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T04:40:39.453205+00:00
-- url     : https://prove2.me/theorems/346ca9db-18e7-4147-8cf7-02e973ab548a
-- title:
--   Physical wall and tangent bounds on angular radial curves
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
--   There exists $C\ge32$. In this estimate the elapsed time
--   is an arbitrary $T\ge0$ with $Ch\le1/4$, $r\le1$, $Mr\le1/16$,
--   $CMrT\le1/8$ and $rT\le1$. Take $0\le\zeta\le r/9$.
--   The radial derivative of $(n_T,Z_T)$ is its section differential in
--   direction $(\theta,1,0)$. The first shear is at most $-15/16$,
--   $0<n_T\le he^{-2T}$, $\|Z_T\|\le Mr$, $(Z_T)_1\ge r/2$ and
--   $0\le(Z_T)_2\le2\zeta$. Each center derivative is bounded by
--   $2(L+1)$; $|n_T'|\le2(L+1)n_T/r$ and
--   $|(Z_T)_2'|\le8C(L+1)(Z_T)_2/r$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/RestartRadialCurveControl.lean#L20-L106

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_SectionRestartData
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
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

noncomputable section
open BianchiIX
open Set

theorem BianchiIX.exists_restartRadialCurve_control :
    ∃ C ≥ (32 : ℝ), ∀ h r T L : ℝ,
      0 < h → C * h ≤ 1 / 4 → (0 < r ∧ r ≤ 1) → 0 ≤ L →
      8 * (L + 1) * r ≤ 1 / 16 → 0 ≤ T → C * (8 * (L + 1) * r) * T ≤ 1 / 8 → r * T ≤ 1 →
      ∀ θ ζ ρ : ℝ, |θ| ≤ L → (0 ≤ ζ ∧ ζ ≤ r / 9) → ρ ∈ Icc r (2 * r) →
        let Z := restartRadialCurve θ ζ ρ
        let p := restartSectionRadialState h T Z
        let v := fderiv ℝ (restartSectionRadialState h T) Z (restartRadialDirection θ)
        HasDerivAt (fun x => restartSectionRadialState h T (restartRadialCurve θ ζ x)) v ρ ∧
        normalizedMaxCurve (restartSectionChart h Z) 0 T 0 ≤ -(15 / 16) ∧
        0 < p.1 ∧ p.1 ≤ h * Real.exp (-2 * T) ∧
        ‖p.2‖ ≤ 8 * (L + 1) * r ∧ r / 2 ≤ p.2 1 ∧
        (0 ≤ p.2 2 ∧ p.2 2 ≤ 2 * ζ) ∧
        (∀ i : Fin 3, |v.2 i| ≤ 2 * (L + 1)) ∧
        |v.1| ≤ 2 * (L + 1) * p.1 / r ∧
        |v.2 2| ≤ 8 * C * (L + 1) * p.2 2 / r := by sorry
