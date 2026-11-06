-- Prove2me | Theorems.Thm_BianchiIX_integral_le_of_exp_decay
-- name    : BianchiIX.integral_le_of_exp_decay
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T00:35:53.26042+00:00
-- url     : https://prove2.me/theorems/8224d57a-0bc3-42ab-b686-10bb6584a083
-- title:
--   Integrating a continuous function below an exponential envelope
-- statement:
--   Let $a\leq b$, $c>0$, $B\geq0$, and let $f$ be
--   continuous on $[a,b]$. If $f(z)\leq B e^{-c(z-a)}$ on $[a,b]$, then
--   $$\int_a^b f(z)\,dz\leq B/c.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/CoreIntegrals.lean#L27-L35

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

theorem BianchiIX.integral_le_of_exp_decay {f : ℝ → ℝ} {a b c B : ℝ} (hab : a ≤ b) (hc : 0 < c)
    (hB : 0 ≤ B) (hf : ContinuousOn f (Icc a b))
    (hbound : ∀ z ∈ Icc a b, f z ≤ B * Real.exp (-c * (z - a))) :
    (∫ z in a..b, f z) ≤ B / c := by sorry
