-- Prove2me | Theorems.Thm_APFPaper1_RecordOccupant_relation_recorded_members_free
-- name    : APFPaper1.RecordOccupant.relation_recorded_members_free
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T22:26:10.65509+00:00
-- url     : https://prove2.me/theorems/c484822d-f776-4c8c-8753-f31cfd2c4ed6
-- title:
--   An equality record fixes the relation while leaving both values unfixed
-- statement:
--   Under EveryCombinationHeld, a record allowing exactly states where two readings agree has a nonempty allowed set, forces their equality, and leaves each reading with both Boolean values allowed.
--
--   Publication scope: Expose nonemptiness, hB02, SpeaksOnlyOf, exact relation/side-record semantics, about and hatom, and nonnegative eps with per-record floor. Do not turn the count into a general dimension bound. B07b does not by this file turn classical uncertainty into ontological absence.
-- source:
--   ['C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/source/Theorems/Thm_APFPaper1_RecordOccupant_sides.lean:124 (source SHA256 939fe95a141626054481d1b351a906318012304610276c68e02f3b08bb26c738; APFPaper1.RecordOccupant.relation_recorded_members_free)', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/reviews/rv2_v66_v22_review.json (SHA256 365ce42aeeada41fa76b7443fe2b5af6017c7fdeb2bb28169266b6dbba622948; modules[Theorems.Thm_APFPaper1_RecordOccupant_sides].declarations[APFPaper1.RecordOccupant.relation_recorded_members_free])']

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

theorem APFPaper1.RecordOccupant.relation_recorded_members_free [DecidableEq D] (reads : D → X → Bool)
    (allows : Rec → X → Prop) (hB02 : APFB02.EveryCombinationHeld reads) (d1 d2 : D) (r : Rec)
    (hr : ∀ x, allows r x ↔ reads d1 x = reads d2 x) :
    (allowed allows {r}).Nonempty ∧ (∀ x ∈ allowed allows {r}, reads d1 x = reads d2 x) ∧
      NoSide reads allows {r} d1 ∧ NoSide reads allows {r} d2 := by sorry
