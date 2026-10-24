-- Prove2me | Theorems.Thm_AvramDividend_Classical_nat_capped_first_hit_eventually_stabilizes
-- name    : AvramDividend.Classical.nat_capped_first_hit_eventually_stabilizes
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T10:11:35.438747+00:00
-- url     : https://prove2.me/theorems/8d0b538e-e6cc-475e-a818-1273e3a18d96
-- title:
--   Capped first discrete hitting indices eventually equal the true earliest hitting index
-- statement:
--   Given any sequence u:Nat→Real and any set s of values which the sequence eventually visits, there is a first index j with u(j)∈s such that for every terminal cap m≥j, the Mathlib hittingBtwn function with start index 0 and cap m equals j. Pick the least witness Nat.find. Use the pinned Mathlib hittingBtwn_mem_set and hittingBtwn_le to show the capped index at j is exactly j, and hittingBtwn_eq_hittingBtwn_of_exists to show it remains equal to j for larger caps. This is the deterministic eventual-stabilisation input needed to pass bounded grid exponential stopping bounds to the true unbounded discrete first-upcrossing time.

import Mathlib.Probability.Process.HittingTime
import Mathlib.Data.Nat.Find
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.nat_capped_first_hit_eventually_stabilizes
    (u : ℕ → ℝ) (s : Set ℝ) (h : ∃ j : ℕ, u j ∈ s) :
    ∃ j : ℕ, u j ∈ s ∧
      ∀ m : ℕ, j ≤ m →
        hittingBtwn (fun k (_ : Unit) => u k) s 0 m () = j := by sorry
