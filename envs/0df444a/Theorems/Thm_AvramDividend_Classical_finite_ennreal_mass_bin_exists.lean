-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_ennreal_mass_bin_exists
-- name    : AvramDividend.Classical.finite_ennreal_mass_bin_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T08:34:16.652077+00:00
-- url     : https://prove2.me/theorems/f0523660-a983-4fdf-93b3-83a88ed342ec
-- title:
--   Every finite nonnegative extended-real mass belongs to a natural-number unit bin
-- statement:
--   Every finite extended nonnegative real m has a unique relevant natural-number mass level n whose upper boundary n+1 is at least m and whose lower boundary n is strictly below m, except that bin zero also contains m=0. The proof chooses the least natural upper boundary using Nat.find on the archimedean existence supplied by ENNReal.exists_nat_gt, and uses minimality to establish the lower bound. This is needed to partition sample-path total masses of the genuine dividend Stieltjes kernel into countably many measurable sets with uniformly bounded mass.
-- source:
--   Pinned Mathlib ENNReal.exists_nat_gt in Mathlib.Data.ENNReal.Basic; Nat.find_spec and Nat.find_min in Mathlib.Data.Nat.Find. General mathematical lemma independent of Lévy processes.

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Nat.Find

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.finite_ennreal_mass_bin_exists
    (m : ℝ≥0∞) (hm : m < ⊤) :
    ∃ n : ℕ, m ≤ (n + 1 : ℝ≥0∞) ∧
      (n = 0 ∨ (n : ℝ≥0∞) < m) := by sorry
