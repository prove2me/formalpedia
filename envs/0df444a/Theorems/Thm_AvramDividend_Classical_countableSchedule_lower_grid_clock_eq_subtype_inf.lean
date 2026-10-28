-- Prove2me | Theorems.Thm_AvramDividend_Classical_countableSchedule_lower_grid_clock_eq_subtype_inf
-- name    : AvramDividend.Classical.countableSchedule_lower_grid_clock_eq_subtype_inf
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:51:38.367926+00:00
-- url     : https://prove2.me/theorems/7bcfe9dc-59bb-4c40-9001-6ab3e90073ae
-- title:
--   The measurable countable-schedule lower clock equals the positive-denominator grid crossing infimum
-- statement:
--   For any real-valued path on nonnegative time, the first lower crossing clock formed by the single countable schedule of inverse-natural mesh points, assigning infinity on noncrossing observations, agrees with the subtype-indexed infimum over every strictly lower-crossing rational grid time with positive denominator. This supplies the lower passage clock identification needed by the Borel full-future-path reward.
-- source:
--   Uses Proved inverseNatural_positive_grid_point_has_nat_schedule_index UUID 7ff3fbf1-05d9-4d01-8074-9b20deeb4793 and Proved firstPassage_iInf_eq_of_strict_horizon_witness_iff UUID 92726415-3249-44ca-b210-3790cce4b6fe. Lower companion to countableSchedule_upper_grid_clock_eq_subtype_inf and strict Lévy lower grid equality 9c8cf4c0-7701-4341-86de-3942142a9bff.

import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Nat.Pairing
import Theorems.Thm_AvramDividend_Classical_firstPassage_iInf_eq_of_strict_horizon_witness_iff
import Theorems.Thm_AvramDividend_Classical_inverseNatural_positive_grid_point_has_nat_schedule_index

open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.countableSchedule_lower_grid_clock_eq_subtype_inf
    (g : ℝ≥0 → ℝ) (lower : ℝ) :
    (⨅ j : ℕ, if
          g (((Nat.unpair j).2 : ℝ≥0) *
            (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)) < lower
        then ((((Nat.unpair j).2 : ℝ≥0) *
          (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)) : ℝ≥0∞)
        else ⊤) =
    (⨅ i : {p : ℕ × ℕ // 0 < p.1 ∧
          g ((p.2 : ℝ≥0) * (p.1 : ℝ≥0)⁻¹) < lower},
      (((i.1.2 : ℝ≥0) * (i.1.1 : ℝ≥0)⁻¹) : ℝ≥0∞)) := by sorry
