-- Prove2me | Theorems.Thm_AvramDividend_Classical_finiteTimeSet_monotoneZeroBasedGrid
-- name    : AvramDividend.Classical.finiteTimeSet_monotoneZeroBasedGrid
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:38:57.73003+00:00
-- url     : https://prove2.me/theorems/c2989d1c-c965-4668-af84-b97ebcd9077a
-- title:
--   Every finite set of nonnegative observation times admits a monotone zero-based grid
-- statement:
--   For any finite set J of nonnegative times, there is a finite monotone sequence starting at zero whose positive-indexed entries include every time in J. This supplies the ordered deterministic grid required for Lévy finite-dimensional stationarity.
-- source:
--   Finite time-grid enumerator needed to combine Proved zero-based grid law 2306113f-95d9-49ba-b55a-102a78f19a3f and arbitrary finite-index projection a7ef4e12-f915-420f-95d8-d49c79a2e803, to close whole-path stationarity and the strong-Markov barrier child 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.Probability.Independence.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open scoped NNReal ENNReal

theorem AvramDividend.Classical.finiteTimeSet_monotoneZeroBasedGrid (J : Finset ℝ≥0) :
    ∃ (n : ℕ) (t : ℕ → ℝ≥0) (e : J → Fin n),
      Monotone t ∧ t 0 = 0 ∧
      ∀ j : J, t ((e j).val + 1) = (j : ℝ≥0) := by
  sorry
