-- Prove2me | Theorems.Thm_AvramDividend_Classical_rightInterval_upper_strictExit_eq_schedule
-- name    : AvramDividend.Classical.rightInterval_upper_strictExit_eq_schedule
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:06:15.438953+00:00
-- url     : https://prove2.me/theorems/d747b9c8-d11b-4d9f-9c58-d39f5aaf3dd0
-- title:
--   Any right-persistent upper exit clock equals an explicit measurable countable schedule
-- statement:
--   For an arbitrary real path whose strict upward threshold crossings persist on a short right interval, the true first strict upward passage infimum agrees with the explicit inverse-natural countable schedule clock, including infinite no-crossing cases. This abstracts away from Lévy processes and supports strong-Markov shifted future-path rewards.
-- source:
--   Compose the generic horizon countable-grid equivalence with the Proved iInf first-passage clock extensionality, then the Proved upper grid-to-countable-schedule equality.

import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Nat.Pairing
import Theorems.Thm_AvramDividend_Classical_rightInterval_upper_before_horizon_grid_iff
import Theorems.Thm_AvramDividend_Classical_firstPassage_iInf_eq_of_strict_horizon_witness_iff
import Theorems.Thm_AvramDividend_Classical_countableSchedule_upper_grid_clock_eq_subtype_inf

open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.rightInterval_upper_strictExit_eq_schedule
    (g : ℝ≥0 → ℝ) (upper : ℝ)
    (hRight : ∀ s : ℝ≥0, upper < g s →
      ∃ u : ℝ≥0, s < u ∧
        ∀ r : ℝ≥0, s ≤ r → r < u → upper < g r) :
    (⨅ i : {t : ℝ≥0 // upper < g t}, (i.1 : ℝ≥0∞)) =
    (⨅ j : ℕ, if upper <
          g (((Nat.unpair j).2 : ℝ≥0) *
            (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹))
        then ((((Nat.unpair j).2 : ℝ≥0) *
          (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)) : ℝ≥0∞)
        else ⊤) := by sorry
