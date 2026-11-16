-- Prove2me | Theorems.Thm_APFPaper1_RecordOccupant_gains_the_allowed_states_side
-- name    : APFPaper1.RecordOccupant.gains_the_allowed_states_side
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T22:20:44.039863+00:00
-- url     : https://prove2.me/theorems/d23e9bbe-57b0-42e9-a428-6e636112f340
-- title:
--   Recording a permitted point's value preserves that point and fixes the reading
-- statement:
--   If K permits x and r permits exactly states with the same d value as x, then adding r still permits x and fixes d to that value.
--
--   Publication scope: The point x is a potential state, not the proposed occupant in raw form. Exact hr/hrt/hrf record semantics and kept membership are explicit. No A2 tie resolution or physical side selection follows.
-- source:
--   ['C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/source/Theorems/Thm_APFPaper1_records_at_a_potential_state.lean:61 (source SHA256 5c0a38b3900d06c1479228111b1231ffd7333f5dadda6a5d93a9fac476afd02b; APFPaper1.RecordOccupant.gains_the_allowed_states_side)', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/reviews/rv2_v66_v22_review.json (SHA256 365ce42aeeada41fa76b7443fe2b5af6017c7fdeb2bb28169266b6dbba622948; modules[Theorems.Thm_APFPaper1_records_at_a_potential_state].declarations[APFPaper1.RecordOccupant.gains_the_allowed_states_side])']

import Definitions.Def_APFPaper1_RecordOccupant
import Mathlib.Data.Finset.Insert

set_option autoImplicit false
namespace APFPaper1.RecordOccupant
end APFPaper1.RecordOccupant
open APFPaper1.RecordOccupant
variable {X D Rec : Type*}

theorem APFPaper1.RecordOccupant.gains_the_allowed_states_side [DecidableEq Rec] (reads : D → X → Bool)
    (allows : Rec → X → Prop) (K : Finset Rec) (x : X) (hx : x ∈ allowed allows K) (d : D)
    (r : Rec) (hr : ∀ y, allows r y ↔ reads d y = reads d x) :
    x ∈ allowed allows (insert r K) ∧ HasSide reads allows (insert r K) d (reads d x) := by sorry
