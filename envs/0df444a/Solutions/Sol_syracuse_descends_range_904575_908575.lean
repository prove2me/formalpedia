-- Prove2me | solution 1 for syracuse_descends_range_904575_908575
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T21:19:41.432978+00:00
-- url     : https://prove2.me/submissions/b44c2e1b-b72f-4790-b852-355cbc9dc06d

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_descends_range_904575_906575
import Theorems.Thm_syracuse_descends_range_906576_908575

theorem solution (m : ℕ) (hlo : 904575 ≤ m) (hhi : m ≤ 908575) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  rcases Nat.lt_or_ge m 906576 with h | h
  · exact syracuse_descends_range_904575_906575 m hlo (by omega) hodd
  · exact syracuse_descends_range_906576_908575 m h hhi hodd
