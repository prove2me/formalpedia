-- Prove2me | solution 1 for syracuse_periodic_ge_seven_eq_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-09T01:51:00.225763+00:00
-- url     : https://prove2.me/submissions/af2e651b-174e-48d7-b306-cdf01bfdd7a9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna
-/
import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_fixed_point_eq_one
import Theorems.Thm_syracuse_two_cycle_eq_one
import Theorems.Thm_syracuse_three_cycle_eq_one
import Theorems.Thm_syracuse_four_cycle_eq_one
import Theorems.Thm_syracuse_five_cycle_eq_one
import Theorems.Thm_syracuse_six_cycle_eq_one
import Theorems.Thm_syracuse_seven_cycle_eq_one
import Theorems.Thm_syracuse_minimal_period_ge_eight_eq_one

/-!
# Periodic Syracuse points via least positive return

This module reduces a return time at least seven to its least positive return.
Returns of lengths one through seven use the corresponding bounded cycle
results; the remaining case is the minimal-period-at-least-eight child.
-/

/-- Reduce an arbitrary return time at least seven to its least positive return. -/
theorem solution (m period : ℕ)
    (hm : 0 < m) (hperiod : 7 ≤ period)
    (hcyc : syracuseStep^[period] m = m) :
    m = 1 := by
  have hreturn : ∃ k : ℕ, 0 < k ∧ syracuseStep^[k] m = m :=
    ⟨period, by omega, hcyc⟩
  let p := Nat.find hreturn
  have hp_spec : 0 < p ∧ syracuseStep^[p] m = m := by
    exact Nat.find_spec hreturn
  have hp_le : p ≤ period := by
    exact Nat.find_min' hreturn ⟨by omega, hcyc⟩
  have hp_cyc : syracuseStep^[p] m = m := hp_spec.2
  by_cases hp_small : p ≤ 7
  · have hp_cases : p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 := by
      omega
    rcases hp_cases with hp1 | hp2 | hp3 | hp4 | hp5 | hp6 | hp7
    · exact syracuse_fixed_point_eq_one m hm (by simpa [hp1] using hp_cyc)
    · exact syracuse_two_cycle_eq_one m hm (by simpa [hp2] using hp_cyc)
    · exact syracuse_three_cycle_eq_one m hm (by simpa [hp3] using hp_cyc)
    · exact syracuse_four_cycle_eq_one m hm (by simpa [hp4] using hp_cyc)
    · exact syracuse_five_cycle_eq_one m hm (by simpa [hp5] using hp_cyc)
    · exact syracuse_six_cycle_eq_one m hm (by simpa [hp6] using hp_cyc)
    · exact syracuse_seven_cycle_eq_one m hm (by simpa [hp7] using hp_cyc)
  · apply syracuse_minimal_period_ge_eight_eq_one m p hm (by omega) hp_cyc
    intro k hkpos hklt hkc
    exact Nat.find_min hreturn hklt ⟨hkpos, hkc⟩
