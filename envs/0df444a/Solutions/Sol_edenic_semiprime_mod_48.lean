-- Prove2me | solution 1 for edenic_semiprime_mod_48
-- status  : ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-26T16:55:27.174413+00:00
-- url     : https://prove2.me/submissions/cf8c2bb0-92b9-4f64-a95d-74efb9418f0d

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_edenic_semiprime_mod_sixteen
import Theorems.Thm_edenic_semiprime_mod_six

theorem solution (n : ℕ) (h : IsEdenicSemiprime n) :
    n % 48 = 35 ∨ n % 48 = 47 ∨ n = 15 := by
  rcases edenic_semiprime_mod_sixteen n h with h16 | h16
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

-- #43
