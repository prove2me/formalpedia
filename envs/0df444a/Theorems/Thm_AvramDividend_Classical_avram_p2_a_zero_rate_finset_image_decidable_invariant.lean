-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_finset_image_decidable_invariant
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_finset_image_decidable_invariant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:18:10.450267+00:00
-- url     : https://prove2.me/theorems/b149bff2-6ee0-4f86-ab20-72ee378a9238
-- title:
--   Finite grid image invariant under proof-relevant decidable equality choices
-- statement:
--   For a finite grid s and endpoint map f, prove that the resulting Finset.image is extensionally identical for any two DecidableEq implementations on endpoint types. This supplies an explicit source-supported Lean bridge between original càdlàg mesh lemmas elaborated with different DecidableEq instances; it is independent of any Levy count rate.

import Mathlib

open Finset

theorem AvramDividend.Classical.avram_p2_a_zero_rate_finset_image_decidable_invariant
    {α β : Type*} (s : Finset α) (f : α → β)
    (d₁ d₂ : DecidableEq β) :
    (@Finset.image α β d₁ f s) = (@Finset.image α β d₂ f s) := by sorry
