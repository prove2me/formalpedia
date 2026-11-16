-- Prove2me | Theorems.Thm_APFPaper1_RecordOccupant_noSide_of_not_spoken_of
-- name    : APFPaper1.RecordOccupant.noSide_of_not_spoken_of
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T22:24:10.610198+00:00
-- url     : https://prove2.me/theorems/4e4755e0-81ab-4313-99b6-179a18d94f2e
-- title:
--   A consistent family cannot fix an unmentioned independent reading
-- statement:
--   Assuming EveryCombinationHeld, if K speaks only of S, K allows a state, and d is outside S, then NoSide holds on d.
--
--   Publication scope: Expose nonemptiness, hB02, SpeaksOnlyOf, exact relation/side-record semantics, about and hatom, and nonnegative eps with per-record floor. Do not turn the count into a general dimension bound. B07b does not by this file turn classical uncertainty into ontological absence.
-- source:
--   ['C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/source/Theorems/Thm_APFPaper1_RecordOccupant_sides.lean:95 (source SHA256 939fe95a141626054481d1b351a906318012304610276c68e02f3b08bb26c738; APFPaper1.RecordOccupant.noSide_of_not_spoken_of)', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/reviews/rv2_v66_v22_review.json (SHA256 365ce42aeeada41fa76b7443fe2b5af6017c7fdeb2bb28169266b6dbba622948; modules[Theorems.Thm_APFPaper1_RecordOccupant_sides].declarations[APFPaper1.RecordOccupant.noSide_of_not_spoken_of])']

import Definitions.Def_APFPaper1_RecordOccupant
import Definitions.Def_APFB02_EachTakesBothSides
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper1.RecordOccupant
end APFPaper1.RecordOccupant
open APFPaper1.RecordOccupant
variable {X D Rec : Type*}

theorem APFPaper1.RecordOccupant.noSide_of_not_spoken_of [DecidableEq D] (reads : D → X → Bool)
    (allows : Rec → X → Prop) (hB02 : APFB02.EveryCombinationHeld reads) (K : Finset Rec)
    (S : Finset D) (hsp : SpeaksOnlyOf reads allows K S) (d : D) (hd : d ∉ S)
    (hne : (allowed allows K).Nonempty) : NoSide reads allows K d := by sorry
