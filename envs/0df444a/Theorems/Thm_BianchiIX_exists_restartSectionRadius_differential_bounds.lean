-- Prove2me | Theorems.Thm_BianchiIX_exists_restartSectionRadius_differential_bounds
-- name    : BianchiIX.exists_restartSectionRadius_differential_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T04:40:10.08049+00:00
-- url     : https://prove2.me/theorems/8ead386b-f9eb-45e2-8e5a-4147cd0ac226
-- title:
--   Initial-data derivatives of the transported radius and its time rate
-- statement:
--   Write $\Phi_t x$ for the normalized vacuum Bianchi IX flow and
--   $x_h(Z)$ for the constraint-one, negative-first-shear chart with primary
--   wall $h$ and center coordinates $Z=(v,b,c)$ (second shear and the other
--   two walls). At time $t$, denote its primary wall by $n_t$ and center by
--   $Z_t$. Set $r(Z)=\sqrt{v^2+(b-c)^2}$. For $u=\sqrt{1-h^2}$ define
--   $A=3/(2+u)$, $B=3\sqrt3 h/(2+u)^2$, $H=9(1+u)/(2(2+u)^2)$,
--   $Q_h(v,w)=(Av+Bw)^2+H^2w^2$ and $F_h(Z)=\sqrt{Q_h(v,b-c)}/\sqrt3$.
--   There is an absolute $C\ge32$. Use $h>0$,
--   $Ch\le1/4$, $0<b_0\le1/16$, $T\ge0$, $Cb_0T\le1/8$ and $0\le t\le T$.
--   For every $c>0$ there is $K>0$ such that for
--   $\|Z\|\le b_0/2$, $r(Z)\ge cb_0$, the transported radius $R_t$
--   (the square root of the quadratic form at the current wall and center)
--   satisfies $R_t\ge cb_0/2$. Both $R_t$ and its time rate are
--   differentiable in $Z$; $\|DR_t\|\le K$ and
--   $\|D\dot R_t\|\le K(n_t b_0+b_0^2)$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/RestartRadiusDifferential.lean#L13-L97

import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
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

noncomputable section
open BianchiIX
open Set

theorem BianchiIX.exists_restartSectionRadius_differential_bounds :
    ∃ C ≥ (32 : ℝ), ∀ c : ℝ, 0 < c → ∃ K : ℝ, 0 < K ∧
      ∀ (h b T : ℝ) (Z : RestartCenterState),
        0 < h → C * h ≤ 1 / 4 → (0 < b ∧ b ≤ 1 / 16) → 0 ≤ T → C * b * T ≤ 1 / 8 →
        ‖Z‖ ≤ b / 2 → c * b ≤ restartRadialNorm Z → ∀ t ∈ Icc (0 : ℝ) T,
          c * b / 2 ≤ restartSectionRadius h t Z ∧
          DifferentiableAt ℝ (restartSectionRadius h t) Z ∧
          ‖fderiv ℝ (restartSectionRadius h t) Z‖ ≤ K ∧
          DifferentiableAt ℝ (restartSectionRadiusRate h t) Z ∧
          ‖fderiv ℝ (restartSectionRadiusRate h t) Z‖ ≤
            K * (restartSectionStrongWall h t Z * b + b ^ 2) := by sorry
