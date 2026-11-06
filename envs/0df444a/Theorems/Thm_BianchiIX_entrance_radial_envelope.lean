-- Prove2me | Theorems.Thm_BianchiIX_entrance_radial_envelope
-- name    : BianchiIX.entrance_radial_envelope
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T06:59:14.208212+00:00
-- url     : https://prove2.me/theorems/080bca46-4349-47d7-9c35-a2af3d7fe247
-- title:
--   Entrance radial errors retain exponential decay in both wall scales
-- statement:
--   Let $k>0$ and $z,u,v,w,U,W\geq0$. Suppose
--   $$U\leq u e^{-(1+k/3)z},\qquad W\leq w e^{-(1+1/k)z},\qquad V=ve^z.$$
--   Then
--   $$U(V+W)+U^2+W^2/k
--   \leq\bigl(u(v+w)+u^2\bigr)e^{-kz/3}+(w^2/k)e^{-2z}.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/EntranceEnvelopes.lean#L7-L39

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX

theorem BianchiIX.entrance_radial_envelope {k z u v w U V W : ℝ} (hk : 0 < k) (hz : 0 ≤ z)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hU0 : 0 ≤ U) (hW0 : 0 ≤ W)
    (hU : U ≤ u * Real.exp (-(1 + k / 3) * z))
    (hW : W ≤ w * Real.exp (-(1 + 1 / k) * z)) (hV : V = v * Real.exp z) :
    U * (V + W) + U ^ 2 + W ^ 2 / k ≤
      (u * (v + w) + u ^ 2) * Real.exp (-(k / 3) * z) +
        (w ^ 2 / k) * Real.exp (-2 * z) := by sorry
