-- Prove2me | Theorems.Thm_BianchiIX_finite_distortion_budget_le
-- name    : BianchiIX.finite_distortion_budget_le
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T16:58:11.624591+00:00
-- url     : https://prove2.me/theorems/8cff5fd6-a9e2-4d69-b7ee-9753d4dee2f9
-- title:
--   A uniform finite distortion budget from summable errors
-- statement:
--   Let $d,e:\mathbb N\to[0,\infty)$ be summable real sequences.
--   For every $n\geq0$,
--   $$\sum_{j=0}^{n-1}\left(e_j+\begin{cases}0&j=0,\\2d_j&j>0\end{cases}\right)
--   \leq\sum_{j=0}^{\infty}e_j+2\sum_{j=0}^{\infty}d_{j+1}.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/StoppedMass.lean#L12-L32

import Definitions.Def_BianchiIX_Statistics_StoppedMass
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

open BianchiIX
noncomputable section
open Set MeasureTheory
open scoped ENNReal

theorem BianchiIX.finite_distortion_budget_le (d e : ℕ → ℝ)
    (hd0 : ∀ j, 0 ≤ d j) (he0 : ∀ j, 0 ≤ e j) (hd : Summable d) (he : Summable e) (n : ℕ) :
    (∑ j ∈ Finset.range n, (e j + if j = 0 then 0 else 2 * d j)) ≤
      (∑' j, e j) + 2 * ∑' j, d (j + 1) := by sorry
