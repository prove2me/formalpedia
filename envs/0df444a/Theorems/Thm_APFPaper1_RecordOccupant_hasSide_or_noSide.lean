-- Prove2me | Theorems.Thm_APFPaper1_RecordOccupant_hasSide_or_noSide
-- name    : APFPaper1.RecordOccupant.hasSide_or_noSide
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T22:22:41.988987+00:00
-- url     : https://prove2.me/theorems/be4edd6c-e89e-4527-9ab4-f34969afaac6
-- title:
--   A nonempty allowed set has one of the three side statuses
-- statement:
--   If the allowed set is nonempty, a Boolean reading is fixed true, fixed false, or takes both values on that set.
--
--   Publication scope: Expose nonemptiness, hB02, SpeaksOnlyOf, exact relation/side-record semantics, about and hatom, and nonnegative eps with per-record floor. Do not turn the count into a general dimension bound. B07b does not by this file turn classical uncertainty into ontological absence.
-- source:
--   ['C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/source/Theorems/Thm_APFPaper1_RecordOccupant_sides.lean:52 (source SHA256 939fe95a141626054481d1b351a906318012304610276c68e02f3b08bb26c738; APFPaper1.RecordOccupant.hasSide_or_noSide)', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/reviews/rv2_v66_v22_review.json (SHA256 365ce42aeeada41fa76b7443fe2b5af6017c7fdeb2bb28169266b6dbba622948; modules[Theorems.Thm_APFPaper1_RecordOccupant_sides].declarations[APFPaper1.RecordOccupant.hasSide_or_noSide])']

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

theorem APFPaper1.RecordOccupant.hasSide_or_noSide (reads : D → X → Bool) (allows : Rec → X → Prop) (K : Finset Rec)
    (hne : (allowed allows K).Nonempty) (d : D) :
    HasSide reads allows K d true ∨ HasSide reads allows K d false ∨ NoSide reads allows K d := by sorry
