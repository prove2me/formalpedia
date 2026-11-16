-- Prove2me | Theorems.Thm_APFPaper1_RecordOccupant_gaining_a_side_gives_record_form
-- name    : APFPaper1.RecordOccupant.gaining_a_side_gives_record_form
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T22:18:03.204195+00:00
-- url     : https://prove2.me/theorems/cd67ebe6-c776-4625-a1b3-2df02a6d8995
-- title:
--   A consistent exact side record fixes that side
-- statement:
--   If r allows exactly the potential states with reading b on d and adding r leaves a nonempty allowed set, the enlarged record set satisfies HasSide for d and b.
--
--   Publication scope: Exact side-record meanings, fresh records and equal record costs remain the respective hypotheses. Equal extended-record costs do not establish global minimization, a nonunique global minimum, a physical side selector or Born probabilities. The corrected header now states this limit.
-- source:
--   ['C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/source/Theorems/Thm_APFPaper1_RecordOccupant_gaining_a_side.lean:59 (source SHA256 aa9f270a9a6858ec1c6435cbbd6508085663dca60fb64f6bfaa1dafc10d0eeae; APFPaper1.RecordOccupant.gaining_a_side_gives_record_form)', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/reviews/rv2_v66_v22_review.json (SHA256 365ce42aeeada41fa76b7443fe2b5af6017c7fdeb2bb28169266b6dbba622948; modules[Theorems.Thm_APFPaper1_RecordOccupant_gaining_a_side].declarations[APFPaper1.RecordOccupant.gaining_a_side_gives_record_form])', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/publication_comment_corrections/CORRECTIONS.json (SHA256 6f0ad9258c91474be90ee49115bd4c4d303f0759a01bbf3b7e7f7c4c3ac4f777; comment-only correction Theorems.Thm_APFPaper1_RecordOccupant_gaining_a_side)']

import Definitions.Def_APFPaper1_RecordOccupant
import Mathlib.Data.Finset.Insert
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

set_option autoImplicit false
namespace APFPaper1.RecordOccupant
end APFPaper1.RecordOccupant
open APFPaper1.RecordOccupant
variable {X D Rec : Type*}

theorem APFPaper1.RecordOccupant.gaining_a_side_gives_record_form [DecidableEq Rec] (reads : D → X → Bool)
    (allows : Rec → X → Prop) (K : Finset Rec) (d : D) (b : Bool) (r : Rec)
    (hr : ∀ y, allows r y ↔ reads d y = b) (hne : (allowed allows (insert r K)).Nonempty) :
    HasSide reads allows (insert r K) d b := by sorry
