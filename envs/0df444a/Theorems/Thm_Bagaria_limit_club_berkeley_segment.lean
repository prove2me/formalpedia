-- Prove2me | Theorems.Thm_Bagaria_limit_club_berkeley_segment
-- name    : Bagaria.limit_club_berkeley_segment
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-19T23:16:53.804046+00:00
-- url     : https://prove2.me/theorems/9d08773f-86a4-4afb-87e8-1de22a4016e2
-- title:
--   Limit club Berkeley cardinals reflect a Berkeley cardinal that is super Reinhardt
-- statement:
--   Theorem of slide 16, the mission's goal: if δ is a limit club Berkeley cardinal in a universe satisfying ZF, then some δ' below δ is a Berkeley cardinal and is super Reinhardt within the rank segment below δ — the formal counterpart of ⟨V_δ, V_{δ+1}⟩ satisfying "There is a Berkeley card. that is super Reinhardt".
-- source:
--   Bagaria (2017), Large Cardinals beyond Choice, AILA XXVI slides, p. 16, Theorem

import Mathlib
import Definitions.Def_Bagaria_arena
import Definitions.Def_Bagaria_reinhardt
import Definitions.Def_Bagaria_berkeley

universe v

namespace Bagaria

open Universe

/-- Theorem of slide 16 — the mission's goal: every limit club Berkeley
cardinal reflects a Berkeley cardinal that is super Reinhardt within its
own rank segment. If δ is a limit club Berkeley cardinal, then some δ'
below δ is a Berkeley cardinal and is super Reinhardt within the segment
below δ — the formal counterpart of ⟨V_δ, V_{δ+1}⟩ satisfying "There is a
Berkeley card. that is super Reinhardt". -/
theorem limit_club_berkeley_segment (U : Universe.{v}) (hZF : SatisfiesZF U.mem)
    (δ : Ordinal.{v}) (h : U.limitClubBerkeley δ) :
    ∃ δ' : Ordinal.{v}, δ' < δ ∧ U.berkeleyBelow δ δ' ∧ U.superReinhardtIn δ δ' := by
  sorry

end Bagaria
