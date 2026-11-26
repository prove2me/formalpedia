-- Prove2me | solution 1 for edenic_semiprime_mod_twelve
-- status  : ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-26T16:55:31.301669+00:00
-- url     : https://prove2.me/submissions/bb0a79a4-173e-497c-ba51-1c663bc10b30

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_edenic_semiprime_mod_four
import Theorems.Thm_edenic_semiprime_mod_six

theorem solution (n : ℕ) (h : IsEdenicSemiprime n) :
    n % 12 = 11 ∨ n = 15 := by
  have h4 := edenic_semiprime_mod_four n h
  rcases edenic_semiprime_mod_six n h with h6 | h15
  · left
    omega
  · right
    exact h15

-- #48
