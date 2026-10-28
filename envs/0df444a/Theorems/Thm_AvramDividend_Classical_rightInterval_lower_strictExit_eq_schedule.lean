-- Prove2me | Theorems.Thm_AvramDividend_Classical_rightInterval_lower_strictExit_eq_schedule
-- name    : AvramDividend.Classical.rightInterval_lower_strictExit_eq_schedule
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:07:13.268027+00:00
-- url     : https://prove2.me/theorems/de0ada30-f254-46cd-b0db-67ad1f8c8341
-- title:
--   Any right-persistent lower exit clock equals an explicit measurable countable schedule
-- statement:
--   For an arbitrary nonnegative-time real path whose strict lower threshold crossings persist for a short right interval, the true strict downward passage infimum equals the explicit countable schedule clock, even when both are infinite. This result can be used for the shifted future increment path after a Lévy stopping time.
-- source:
--   Compose the generic lower finite-horizon grid equivalence with the Proved first-passage infimum extensionality and the Proved lower grid-to-countable-schedule equality.

import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Nat.Pairing
import Theorems.Thm_AvramDividend_Classical_rightInterval_lower_before_horizon_grid_iff
import Theorems.Thm_AvramDividend_Classical_firstPassage_iInf_eq_of_strict_horizon_witness_iff
import Theorems.Thm_AvramDividend_Classical_countableSchedule_lower_grid_clock_eq_subtype_inf

open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.rightInterval_lower_strictExit_eq_schedule
    (g : ℝ≥0 → ℝ) (lower : ℝ)
    (hRight : ∀ s : ℝ≥0, g s < lower →
      ∃ u : ℝ≥0, s < u ∧
        ∀ r : ℝ≥0, s ≤ r → r < u → g r < lower) :
    (⨅ i : {t : ℝ≥0 // g t < lower}, (i.1 : ℝ≥0∞)) =
    (⨅ j : ℕ, if
          g (((Nat.unpair j).2 : ℝ≥0) *
            (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)) < lower
        then ((((Nat.unpair j).2 : ℝ≥0) *
          (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)) : ℝ≥0∞)
        else ⊤) := by sorry
