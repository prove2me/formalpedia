-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussianB_original_stopped_physmesh_occupation_exact_full_interval
-- name    : AvramDividend.Classical.avram_gaussianB_original_stopped_physmesh_occupation_exact_full_interval
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T07:18:03.462531+00:00
-- url     : https://prove2.me/theorems/d42df514-dd2b-4c14-9ef1-4585c2229fec
-- title:
--   Exact original finite-horizon stopped upper-strip occupation equals T on a precontact Gaussian tube
-- statement:
--   For a physical horizon T within integer n, an original Gaussian reserve above the fixed strip b throughout 0<t<T makes the genuine stopped occupation functional ∫_{(0,n)} 1_{t<T and b<f(toNNReal t)}dt exactly equal T. This directly matches the Occ integral of the original positive-drift fixed-j proof target and quantifies the omitted charge without changing the source stopping clock.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Tactic.NormNum
open MeasureTheory Set
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gaussianB_original_stopped_physmesh_occupation_exact_full_interval
    (f : ℝ≥0 → ℝ) (b : ℝ) (T : ℝ≥0) (n : ℕ)
    (hT : 0 < T) (hTn : (T : ℝ) ≤ (n : ℝ))
    (hFloor : ∀ t : ℝ, 0 < t → t < (T : ℝ) →
      b < f (Real.toNNReal t)) :
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      (if t < (T : ℝ) ∧ b < f (Real.toNNReal t)
        then (1 : ℝ) else 0) ∂volume) = (T : ℝ) := by sorry
