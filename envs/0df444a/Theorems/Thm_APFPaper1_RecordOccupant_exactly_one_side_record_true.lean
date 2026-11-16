-- Prove2me | Theorems.Thm_APFPaper1_RecordOccupant_exactly_one_side_record_true
-- name    : APFPaper1.RecordOccupant.exactly_one_side_record_true
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T22:17:55.854921+00:00
-- url     : https://prove2.me/theorems/89addd2f-efa4-44b5-9a93-6eb6d1a6483e
-- title:
--   Exactly one exact side record permits a given potential state
-- statement:
--   If rt and rf permit exactly the true and false states of d respectively, any given potential state is permitted by exactly one of them.
--
--   Publication scope: The point x is a potential state, not the proposed occupant in raw form. Exact hr/hrt/hrf record semantics and kept membership are explicit. No A2 tie resolution or physical side selection follows.
-- source:
--   ['C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/source/Theorems/Thm_APFPaper1_records_at_a_potential_state.lean:45 (source SHA256 5c0a38b3900d06c1479228111b1231ffd7333f5dadda6a5d93a9fac476afd02b; APFPaper1.RecordOccupant.exactly_one_side_record_true)', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/reviews/rv2_v66_v22_review.json (SHA256 365ce42aeeada41fa76b7443fe2b5af6017c7fdeb2bb28169266b6dbba622948; modules[Theorems.Thm_APFPaper1_records_at_a_potential_state].declarations[APFPaper1.RecordOccupant.exactly_one_side_record_true])']

import Definitions.Def_APFPaper1_RecordOccupant
import Mathlib.Data.Finset.Insert

set_option autoImplicit false
namespace APFPaper1.RecordOccupant
end APFPaper1.RecordOccupant
open APFPaper1.RecordOccupant
variable {X D Rec : Type*}

theorem APFPaper1.RecordOccupant.exactly_one_side_record_true (reads : D → X → Bool) (allows : Rec → X → Prop) (d : D)
    (rt rf : Rec) (hrt : ∀ y, allows rt y ↔ reads d y = true)
    (hrf : ∀ y, allows rf y ↔ reads d y = false) (x : X) :
    (allows rt x ∧ ¬ allows rf x) ∨ (allows rf x ∧ ¬ allows rt x) := by sorry
