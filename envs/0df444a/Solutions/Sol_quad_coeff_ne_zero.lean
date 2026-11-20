-- Prove2me | solution 1 for quad_coeff_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:51:04.243473+00:00
-- url     : https://prove2.me/submissions/fb919456-387d-43d8-b5ba-0f79c1cfa7bc

import Mathlib
import Definitions.Def_LisonekSaltConic

set_option autoImplicit true
open Matrix
variable (p : ℕ) [Fact p.Prime]
theorem _root_.solution (n w2 w4 : ZMod p) (hn : ¬ IsSquare n)
    (hw : (w2, w4) ≠ (0, 0)) : w4^2 * n⁻¹ - w2^2 ≠ 0 := by
  intro h
  have hn0 : n ≠ 0 := by rintro rfl; exact hn ⟨0, by simp⟩
  have h' : w4^2 = n * w2^2 := by field_simp at h; linear_combination h
  by_cases h2 : w2 = 0
  · subst h2
    have : w4 = 0 := by simpa using h'
    exact hw (by simp [this])
  · apply hn
    refine ⟨w4 / w2, ?_⟩
    field_simp
    linear_combination -h'
