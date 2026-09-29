-- Prove2me | solution 1 for flt5_5dvd_c5_of_5dvd_c
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T07:25:22.219544+00:00
-- url     : https://prove2.me/submissions/582f8614-fa17-4d9f-afa2-607b0c9389dd

import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

theorem solution (c : ℤ) (h5c : (5 : ℤ) ∣ c) : (5 : ℤ) ∣ c ^ 5 := by
  obtain ⟨k, hk⟩ := h5c
  exact ⟨5 ^ 4 * k ^ 5, by rw [hk]; ring⟩
