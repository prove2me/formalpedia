-- Prove2me | Theorems.Thm_APFPaper1_RecordOccupant_relation_and_one_side_fix_the_other
-- name    : APFPaper1.RecordOccupant.relation_and_one_side_fix_the_other
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T22:26:11.072709+00:00
-- url     : https://prove2.me/theorems/1c5ff580-12bc-45b4-bbfc-96b4b6325cd3
-- title:
--   An equality record plus one exact side fixes the other reading
-- statement:
--   Under EveryCombinationHeld, retaining an exact equality record for d1,d2 and an exact record that d1=b makes HasSide hold for d2 and b.
--
--   Publication scope: Expose nonemptiness, hB02, SpeaksOnlyOf, exact relation/side-record semantics, about and hatom, and nonnegative eps with per-record floor. Do not turn the count into a general dimension bound. B07b does not by this file turn classical uncertainty into ontological absence.
-- source:
--   ['C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/source/Theorems/Thm_APFPaper1_RecordOccupant_sides.lean:151 (source SHA256 939fe95a141626054481d1b351a906318012304610276c68e02f3b08bb26c738; APFPaper1.RecordOccupant.relation_and_one_side_fix_the_other)', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/reviews/rv2_v66_v22_review.json (SHA256 365ce42aeeada41fa76b7443fe2b5af6017c7fdeb2bb28169266b6dbba622948; modules[Theorems.Thm_APFPaper1_RecordOccupant_sides].declarations[APFPaper1.RecordOccupant.relation_and_one_side_fix_the_other])']

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

theorem APFPaper1.RecordOccupant.relation_and_one_side_fix_the_other [DecidableEq D] [DecidableEq Rec]
    (reads : D → X → Bool) (allows : Rec → X → Prop) (hB02 : APFB02.EveryCombinationHeld reads)
    (d1 d2 : D) (r r1 : Rec) (b : Bool)
    (hr : ∀ x, allows r x ↔ reads d1 x = reads d2 x)
    (hr1 : ∀ x, allows r1 x ↔ reads d1 x = b) :
    HasSide reads allows {r, r1} d2 b := by sorry
