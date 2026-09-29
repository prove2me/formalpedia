-- Prove2me | solution 1 for syracuse_no_cycle_below_12825
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T04:32:56.918267+00:00
-- url     : https://prove2.me/submissions/5c4609e4-f9b4-43b1-a53a-2bf12ea2be71

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_periodic_reaches_one
import Theorems.Thm_syracuse_reaches_one_below_12825

open Nat

theorem stepOdd (n : ℕ) : Odd (syracuseStep n) := by
  rw [Nat.odd_iff, ← Nat.not_even_iff]
  intro he
  exact Nat.not_dvd_ordCompl Nat.prime_two (by omega : 3 * n + 1 ≠ 0) he.two_dvd

theorem solution (z a : ℕ) (hz : 0 < z) (ha : 0 < a) (hle : z ≤ 12824)
    (hcyc : syracuseStep^[a] z = z) : z = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, a = n + 1 := ⟨a - 1, by omega⟩
  have hodd : Odd z := by
    rw [← hcyc, Function.iterate_succ_apply']
    exact stepOdd _
  exact syracuse_periodic_reaches_one z (n + 1) (by omega) hcyc
    (syracuse_reaches_one_below_12825 z hz hodd hle)
