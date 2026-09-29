-- Prove2me | solution 1 for mme_dwz_q6_121_211_component_even_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T09:53:53.939392+00:00
-- url     : https://prove2.me/submissions/7024b576-3828-44fb-9dd7-eee47da4edbe

import Mathlib.Tactic
import Definitions.Def_mme_dwz_table2_integer_counts

open MME

set_option autoImplicit false

theorem solution
    (s : Fin 15) (hs : s = 13 ∨ s = 14) (m : ℕ) :
    MME.DWZTable2Counts.component s * m =
      2 * (1036722900000000 * m) := by
  rcases hs with rfl | rfl
  all_goals change 2073445800000000 * m =
    2 * (1036722900000000 * m)
  all_goals omega
