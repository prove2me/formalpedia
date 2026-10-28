-- Prove2me | Theorems.Thm_Bagaria_club_berkeley_totally_reinhardt
-- name    : Bagaria.club_berkeley_totally_reinhardt
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-19T23:15:27.488846+00:00
-- url     : https://prove2.me/theorems/fc8d63db-efd4-4763-ba24-3f26c6cc1a4c
-- title:
--   Club Berkeley cardinals are totally Reinhardt
-- statement:
--   Theorem of slide 15: every club Berkeley cardinal is totally Reinhardt. Regularity plus the requirement that the critical points of the elementary self-embeddings meet every club subset of δ give enough choiceless embedding structure to see every class of the segment below δ as containing an A-super Reinhardt cardinal within the segment.
-- source:
--   Bagaria (2017), Large Cardinals beyond Choice, AILA XXVI slides, p. 15, Theorem

import Mathlib
import Definitions.Def_Bagaria_arena
import Definitions.Def_Bagaria_reinhardt
import Definitions.Def_Bagaria_berkeley

universe v

namespace Bagaria

open Universe

/-- Theorem of slide 15: every club Berkeley cardinal is totally
Reinhardt. Regularity, plus critical points of the elementary
self-embeddings meeting every club of δ, give enough embedding structure
that the rank segment below δ satisfies ZF and, for every class A of the
segment, contains an A-super Reinhardt cardinal. -/
theorem club_berkeley_totally_reinhardt (U : Universe.{v}) (hZF : SatisfiesZF U.mem)
    (δ : Ordinal.{v}) (hC : U.clubBerkeley δ) :
    U.isTotallyReinhardt δ := by
  sorry

end Bagaria
