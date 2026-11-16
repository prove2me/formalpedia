-- Prove2me | Theorems.Thm_APFPaper1_RecordOccupant_settled_card_le_records
-- name    : APFPaper1.RecordOccupant.settled_card_le_records
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T22:26:11.061883+00:00
-- url     : https://prove2.me/theorems/60e8e1fa-c8a0-4897-8a2b-fa6b3e8935c4
-- title:
--   Atomic records bound the number of fixed readings
-- statement:
--   Under EveryCombinationHeld, if each record in K depends only on its assigned single distinction, any finite family whose members have fixed sides under K has cardinality at most that of K.
--
--   Publication scope: Expose nonemptiness, hB02, SpeaksOnlyOf, exact relation/side-record semantics, about and hatom, and nonnegative eps with per-record floor. Do not turn the count into a general dimension bound. B07b does not by this file turn classical uncertainty into ontological absence.
-- source:
--   ['C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/source/Theorems/Thm_APFPaper1_RecordOccupant_sides.lean:175 (source SHA256 939fe95a141626054481d1b351a906318012304610276c68e02f3b08bb26c738; APFPaper1.RecordOccupant.settled_card_le_records)', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/reviews/rv2_v66_v22_review.json (SHA256 365ce42aeeada41fa76b7443fe2b5af6017c7fdeb2bb28169266b6dbba622948; modules[Theorems.Thm_APFPaper1_RecordOccupant_sides].declarations[APFPaper1.RecordOccupant.settled_card_le_records])']

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

theorem APFPaper1.RecordOccupant.settled_card_le_records [DecidableEq D] (reads : D → X → Bool)
    (allows : Rec → X → Prop) (hB02 : APFB02.EveryCombinationHeld reads) (K : Finset Rec)
    (about : Rec → D)
    (hatom : ∀ r ∈ K, ∀ x y : X, reads (about r) x = reads (about r) y → allows r x → allows r y)
    (T : Finset D) (hT : ∀ d ∈ T, ∃ b, HasSide reads allows K d b) : T.card ≤ K.card := by sorry
