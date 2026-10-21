-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_positive_count_finite_prefix_measurable
-- name    : AvramDividend.Classical.chat06_positive_count_finite_prefix_measurable
-- status  : Open
-- author  : @WillR
-- created : 2026-10-20T15:52:52.89184+00:00
-- url     : https://prove2.me/theorems/e9d5f2c0-ed50-450f-89dd-ebdd809fca4e
-- title:
--   Measurability of the finite arrival-time selection cylinder
-- statement:
--   The condition that a clock time lies between two successive cumulative waiting-time sums is a measurable event of the finite vector of waits.
-- source:
--   Verified source complete private candidate at pinned Mathlib revision; source and remote job recorded in Chat 06 SUBMISSIONS.json. Preamble defines the local arrival/prefix functions used by exact statement.

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Data.Fin.Basic

open MeasureTheory Set
namespace AvramChat06
def padWaitPrefix (n : ℕ) (g : Fin (n + 2) → ℝ) (i : ℕ) : ℝ :=
  if h : i < n + 2 then g ⟨i, h⟩ else 0


def positiveCountPrefixEvent (n : ℕ) (t : ℝ) :
    Set (Fin (n + 2) → ℝ) :=
  {g | (∑ j ∈ Finset.range (n + 1), padWaitPrefix n g j) ≤ t ∧
    t < ∑ j ∈ Finset.range (n + 2), padWaitPrefix n g j}


end AvramChat06
open AvramChat06

theorem AvramDividend.Classical.chat06_positive_count_finite_prefix_measurable (n : ℕ) (t : ℝ) :
    MeasurableSet (positiveCountPrefixEvent n t) := by sorry
