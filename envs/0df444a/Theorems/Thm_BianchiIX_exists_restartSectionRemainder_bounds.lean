-- Prove2me | Theorems.Thm_BianchiIX_exists_restartSectionRemainder_bounds
-- name    : BianchiIX.exists_restartSectionRemainder_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T04:40:16.040928+00:00
-- url     : https://prove2.me/theorems/503cddc3-b4c6-4b10-95e0-8ab115bfdc17
-- title:
--   A quadratic section remainder with an exponentially decaying linear term
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
--   On $\|Z\|\le b_0/2$, let $E_t=Z_t-L_h Z$,
--   where $L_h$ is the limiting center transfer of the reference orbit.
--   $E_t$ is differentiable and satisfies $\|E_t\|\le4Ct\|Z\|^2+
--   6he^{-2t}\|Z\|$ and $\|DE_t\|\le8Ct\|Z\|+6he^{-2t}$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/RestartRemainder.lean#L60-L76

import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
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

noncomputable section
open BianchiIX
open Set

theorem BianchiIX.exists_restartSectionRemainder_bounds :
    ∃ C ≥ (32 : ℝ), ∀ (h b T : ℝ),
      0 < h → C * h ≤ 1 / 4 → (0 < b ∧ b ≤ 1 / 16) → 0 ≤ T → C * b * T ≤ 1 / 8 →
      ∀ t ∈ Icc (0 : ℝ) T, ∀ Z : RestartCenterState, ‖Z‖ ≤ b / 2 →
        DifferentiableAt ℝ (restartSectionRemainder h t) Z ∧
        ‖restartSectionRemainder h t Z‖ ≤ 4 * C * t * ‖Z‖ ^ 2 + 6 * h * Real.exp (-2 * t) * ‖Z‖ ∧
        ‖fderiv ℝ (restartSectionRemainder h t) Z‖ ≤ 8 * C * t * ‖Z‖ + 6 * h * Real.exp (-2 * t) := by sorry
