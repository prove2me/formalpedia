-- Prove2me | Theorems.Thm_BianchiIX_gauss_log_tail_sum
-- name    : BianchiIX.gauss_log_tail_sum
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T16:24:19.167911+00:00
-- url     : https://prove2.me/theorems/c93586f8-52b1-4b90-a06b-1658af1ac9f4
-- title:
--   A telescoping sum of Gauss digit tails
-- statement:
--   For every integer $R\geq0$,
--   $$\sum_{j=0}^{R-1}\frac{\log(1+1/(j+1))}{\log2}
--   =\frac{\log(R+1)}{\log2}.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussMeasure.lean#L155-L170

import Definitions.Def_BianchiIX_Statistics_GaussMeasure
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.PNat.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.WithDensity

open Set MeasureTheory
open scoped ENNReal
open BianchiIX
noncomputable section

theorem BianchiIX.gauss_log_tail_sum (R : ℕ) :
    (∑ j ∈ Finset.range R, Real.log (1 + 1 / ((j : ℝ) + 1)) / Real.log 2) =
      Real.log ((R : ℝ) + 1) / Real.log 2 := by sorry
