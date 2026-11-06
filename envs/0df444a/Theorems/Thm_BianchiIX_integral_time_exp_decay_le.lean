-- Prove2me | Theorems.Thm_BianchiIX_integral_time_exp_decay_le
-- name    : BianchiIX.integral_time_exp_decay_le
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T01:54:31.416817+00:00
-- url     : https://prove2.me/theorems/3ca5e855-0593-4a4f-9b5e-88eb4bca8a84
-- title:
--   The first moment of an exponential decay envelope has a uniform integral bound
-- statement:
--   For $a\leq b$ and $c>0$,
--   $$\int_a^b(t-a)e^{-c(t-a)}\,dt\leq\frac1{c^2}.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ForcedDecayIntegrals.lean#L9-L23

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

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set MeasureTheory

theorem BianchiIX.integral_time_exp_decay_le {a b c : ℝ} (hab : a ≤ b) (hc : 0 < c) :
    (∫ t in a..b, (t - a) * Real.exp (-c * (t - a))) ≤ 1 / c ^ 2 := by sorry
