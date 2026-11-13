-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb26b_real_clock_mapped_positive_mask_eq
-- name    : AvramDividend.Classical.avram_bvb26b_real_clock_mapped_positive_mask_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T16:28:21.521449+00:00
-- url     : https://prove2.me/theorems/cdb0cff2-4a99-4aeb-8b1e-be5b9e95a7c1
-- title:
--   Original mapped nonnegative time mask equals real positive mask on the finite real clock
-- statement:
--   On the genuine nonnegative time image of the original real-time window [0,T], the positive-time and inner-horizon mask using Real.toNNReal is exactly the corresponding real-time mask. This is the measurability-preserving cast bridge between original marked compensation and real-time uniform-grid Lebesgue integral, including the zero boundary via strict positivity.
-- source:
--   Mathlib Real.toNNReal, Set.Icc restricted measure AE membership, integral_congr_ae. Original K real-time bridge 9ace2e92, source-exact 7ccc2a1a.

import Mathlib
open MeasureTheory Set
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb26b_real_clock_mapped_positive_mask_eq
    (T a : ℝ) (f : ℝ≥0 → ℝ) (p : ℝ≥0 → Prop)
    [DecidablePred p] :
    (∫ r in Set.Icc (0 : ℝ) T,
      (if 0 < Real.toNNReal r ∧
          ((Real.toNNReal r : ℝ≥0) : ℝ) < a ∧ p (Real.toNNReal r)
       then f (Real.toNNReal r) else 0)) =
    (∫ r in Set.Icc (0 : ℝ) T,
      (if 0 < r ∧ r < a ∧ p (Real.toNNReal r)
       then f (Real.toNNReal r) else 0)) := by sorry
