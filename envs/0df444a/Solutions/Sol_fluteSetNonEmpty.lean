-- Prove2me | solution 1 for fluteSetNonEmpty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:10:20.767169+00:00
-- url     : https://prove2.me/submissions/b6bf38fe-b172-4c6a-abac-e719c87cf4ae

import Definitions.Def_FriezePatterns_chapter1
import Definitions.Def_FriezePatterns_chapter2

set_option autoImplicit true

theorem _root_.solution (n : ℕ) : Nonempty (fluteSet n) := by
  rcases csteFlute n with ⟨f⟩
  use f
  rfl
