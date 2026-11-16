-- Prove2me | Theorems.Thm_APFPaper1_RecordOccupant_both_sides_can_be_gained
-- name    : APFPaper1.RecordOccupant.both_sides_can_be_gained
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T22:18:02.54104+00:00
-- url     : https://prove2.me/theorems/5116566e-8693-4a09-8054-5533bd82b7b7
-- title:
--   Either exact side record preserves some allowed potential state
-- statement:
--   If the current records permit both Boolean values of d, and rt/rf allow exactly the true/false potential states respectively, adding either record leaves a nonempty allowed set.
--
--   Publication scope: Exact side-record meanings, fresh records and equal record costs remain the respective hypotheses. Equal extended-record costs do not establish global minimization, a nonunique global minimum, a physical side selector or Born probabilities. The corrected header now states this limit.
-- source:
--   ['C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/source/Theorems/Thm_APFPaper1_RecordOccupant_gaining_a_side.lean:43 (source SHA256 aa9f270a9a6858ec1c6435cbbd6508085663dca60fb64f6bfaa1dafc10d0eeae; APFPaper1.RecordOccupant.both_sides_can_be_gained)', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/reviews/rv2_v66_v22_review.json (SHA256 365ce42aeeada41fa76b7443fe2b5af6017c7fdeb2bb28169266b6dbba622948; modules[Theorems.Thm_APFPaper1_RecordOccupant_gaining_a_side].declarations[APFPaper1.RecordOccupant.both_sides_can_be_gained])', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/publication_comment_corrections/CORRECTIONS.json (SHA256 6f0ad9258c91474be90ee49115bd4c4d303f0759a01bbf3b7e7f7c4c3ac4f777; comment-only correction Theorems.Thm_APFPaper1_RecordOccupant_gaining_a_side)']

import Definitions.Def_APFPaper1_RecordOccupant
import Mathlib.Data.Finset.Insert
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

set_option autoImplicit false
namespace APFPaper1.RecordOccupant
end APFPaper1.RecordOccupant
open APFPaper1.RecordOccupant
variable {X D Rec : Type*}

theorem APFPaper1.RecordOccupant.both_sides_can_be_gained [DecidableEq Rec] (reads : D → X → Bool)
    (allows : Rec → X → Prop) (K : Finset Rec) (d : D) (hraw : NoSide reads allows K d)
    (rt rf : Rec) (hrt : ∀ y, allows rt y ↔ reads d y = true)
    (hrf : ∀ y, allows rf y ↔ reads d y = false) :
    (allowed allows (insert rt K)).Nonempty ∧ (allowed allows (insert rf K)).Nonempty := by sorry
