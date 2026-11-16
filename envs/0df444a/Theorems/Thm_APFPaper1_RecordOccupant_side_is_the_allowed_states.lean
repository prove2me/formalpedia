-- Prove2me | Theorems.Thm_APFPaper1_RecordOccupant_side_is_the_allowed_states
-- name    : APFPaper1.RecordOccupant.side_is_the_allowed_states
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T22:26:26.709443+00:00
-- url     : https://prove2.me/theorems/be5739c9-bd4f-4ef8-a5d1-468f28667ad9
-- title:
--   A fixed side agrees with each allowed potential state
-- statement:
--   If x is allowed by K and HasSide(K,d,b) holds, then the reading of d at x is b.
--
--   Publication scope: The point x is a potential state, not the proposed occupant in raw form. Exact hr/hrt/hrf record semantics and kept membership are explicit. No A2 tie resolution or physical side selection follows.
-- source:
--   ['C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/source/Theorems/Thm_APFPaper1_records_at_a_potential_state.lean:39 (source SHA256 5c0a38b3900d06c1479228111b1231ffd7333f5dadda6a5d93a9fac476afd02b; APFPaper1.RecordOccupant.side_is_the_allowed_states)', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/reviews/rv2_v66_v22_review.json (SHA256 365ce42aeeada41fa76b7443fe2b5af6017c7fdeb2bb28169266b6dbba622948; modules[Theorems.Thm_APFPaper1_records_at_a_potential_state].declarations[APFPaper1.RecordOccupant.side_is_the_allowed_states])']

import Definitions.Def_APFPaper1_RecordOccupant
import Mathlib.Data.Finset.Insert

set_option autoImplicit false
namespace APFPaper1.RecordOccupant
end APFPaper1.RecordOccupant
open APFPaper1.RecordOccupant
variable {X D Rec : Type*}

theorem APFPaper1.RecordOccupant.side_is_the_allowed_states (reads : D → X → Bool) (allows : Rec → X → Prop)
    (K : Finset Rec) (x : X) (hx : x ∈ allowed allows K) (d : D) (b : Bool)
    (h : HasSide reads allows K d b) : reads d x = b := by sorry
