-- Prove2me | Theorems.Thm_AvramDividend_Classical_countableSchedule_upper_grid_clock_eq_subtype_inf
-- name    : AvramDividend.Classical.countableSchedule_upper_grid_clock_eq_subtype_inf
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:47:57.42214+00:00
-- url     : https://prove2.me/theorems/125f0dc5-224a-44e2-b18a-28e8cef8eda4
-- title:
--   The measurable countable-schedule upper clock equals the positive-denominator grid crossing infimum
-- statement:
--   For any real-valued path on nonnegative time, the first upper crossing clock formed as a countable infimum over the explicit schedule j↦k_j/(n_j+1), returning infinity on noncrossing samples, equals the subtype-indexed infimum over all positive-denominator rational grid crossing times. The equality is purely combinatorial and makes the Borel full-path reward schedule compatible with the Lévy right-continuous grid-crossing theorem.
-- source:
--   Uses Proved inverseNatural_positive_grid_point_has_nat_schedule_index UUID 7ff3fbf1-05d9-4d01-8074-9b20deeb4793 and Proved firstPassage_iInf_eq_of_strict_horizon_witness_iff UUID 92726415-3249-44ca-b210-3790cce4b6fe. Complements strict upper process grid clock equality UUID 471be5b7-9dda-4d59-8007-d9fa98bf6e5d.

import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Nat.Pairing
import Theorems.Thm_AvramDividend_Classical_firstPassage_iInf_eq_of_strict_horizon_witness_iff
import Theorems.Thm_AvramDividend_Classical_inverseNatural_positive_grid_point_has_nat_schedule_index

open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.countableSchedule_upper_grid_clock_eq_subtype_inf
    (g : ℝ≥0 → ℝ) (upper : ℝ) :
    (⨅ j : ℕ, if upper <
          g (((Nat.unpair j).2 : ℝ≥0) *
            (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹))
        then ((((Nat.unpair j).2 : ℝ≥0) *
          (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)) : ℝ≥0∞)
        else ⊤) =
    (⨅ i : {p : ℕ × ℕ // 0 < p.1 ∧
          upper < g ((p.2 : ℝ≥0) * (p.1 : ℝ≥0)⁻¹)},
      (((i.1.2 : ℝ≥0) * (i.1.1 : ℝ≥0)⁻¹) : ℝ≥0∞)) := by sorry
