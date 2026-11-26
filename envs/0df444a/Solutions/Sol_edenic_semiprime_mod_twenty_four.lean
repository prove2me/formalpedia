-- Prove2me | solution 1 for edenic_semiprime_mod_twenty_four
-- status  : ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-26T16:55:18.340244+00:00
-- url     : https://prove2.me/submissions/1dc14a18-2df2-45b5-a650-1197058ca699

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_edenic_semiprime_mod_eight
import Theorems.Thm_edenic_semiprime_mod_six

theorem solution (n : ℕ) (h : IsEdenicSemiprime n) :
    n % 24 = 11 ∨ n % 24 = 23 ∨ n = 15 := by
  rcases edenic_semiprime_mod_eight n h with h8 | h8
  · rcases edenic_semiprime_mod_six n h with h6 | h15
    · left
      omega
    · right
      right
      exact h15
  · rcases edenic_semiprime_mod_six n h with h6 | h15
    · right
      left
      omega
    · right
      right
      exact h15

-- #42
