-- Prove2me | Theorems.Thm_APFPaper1_RecordOccupant_other_side_never_after
-- name    : APFPaper1.RecordOccupant.other_side_never_after
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T22:25:56.21225+00:00
-- url     : https://prove2.me/theorems/d304ddf9-fd30-4188-85a5-7b3655a85c1c
-- title:
--   Retaining exact opposite side records allows no potential state
-- statement:
--   If K already contains an exact record for side b of d, adding an exact record for the opposite side makes the allowed set empty.
--
--   Publication scope: The point x is a potential state, not the proposed occupant in raw form. Exact hr/hrt/hrf record semantics and kept membership are explicit. No A2 tie resolution or physical side selection follows.
-- source:
--   ['C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/source/Theorems/Thm_APFPaper1_records_at_a_potential_state.lean:85 (source SHA256 5c0a38b3900d06c1479228111b1231ffd7333f5dadda6a5d93a9fac476afd02b; APFPaper1.RecordOccupant.other_side_never_after)', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/reviews/rv2_v66_v22_review.json (SHA256 365ce42aeeada41fa76b7443fe2b5af6017c7fdeb2bb28169266b6dbba622948; modules[Theorems.Thm_APFPaper1_records_at_a_potential_state].declarations[APFPaper1.RecordOccupant.other_side_never_after])']

import Definitions.Def_APFPaper1_RecordOccupant
import Mathlib.Data.Finset.Insert

set_option autoImplicit false
namespace APFPaper1.RecordOccupant
end APFPaper1.RecordOccupant
open APFPaper1.RecordOccupant
variable {X D Rec : Type*}

theorem APFPaper1.RecordOccupant.other_side_never_after [DecidableEq Rec] (reads : D → X → Bool)
    (allows : Rec → X → Prop) (K : Finset Rec) (d : D) (b : Bool) (r r' : Rec) (hrK : r ∈ K)
    (hr : ∀ y, allows r y ↔ reads d y = b) (hr' : ∀ y, allows r' y ↔ reads d y = !b) :
    allowed allows (insert r' K) = ∅ := by sorry
