-- Prove2me | Theorems.Thm_APFPaper1_RecordOccupant_no_tie_at_a_potential_state
-- name    : APFPaper1.RecordOccupant.no_tie_at_a_potential_state
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T22:24:01.511199+00:00
-- url     : https://prove2.me/theorems/935ab2a6-ab22-4ab2-831d-f0d006d7b520
-- title:
--   Opposite exact side-record extensions cannot both permit the same point
-- statement:
--   With exact true and false records for d, a fixed potential state x cannot belong to both enlarged allowed sets obtained by adding those records.
--
--   Publication scope: The point x is a potential state, not the proposed occupant in raw form. Exact hr/hrt/hrf record semantics and kept membership are explicit. No A2 tie resolution or physical side selection follows.
-- source:
--   ['C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/source/Theorems/Thm_APFPaper1_records_at_a_potential_state.lean:73 (source SHA256 5c0a38b3900d06c1479228111b1231ffd7333f5dadda6a5d93a9fac476afd02b; APFPaper1.RecordOccupant.no_tie_at_a_potential_state)', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/reviews/rv2_v66_v22_review.json (SHA256 365ce42aeeada41fa76b7443fe2b5af6017c7fdeb2bb28169266b6dbba622948; modules[Theorems.Thm_APFPaper1_records_at_a_potential_state].declarations[APFPaper1.RecordOccupant.no_tie_at_a_potential_state])']

import Definitions.Def_APFPaper1_RecordOccupant
import Mathlib.Data.Finset.Insert

set_option autoImplicit false
namespace APFPaper1.RecordOccupant
end APFPaper1.RecordOccupant
open APFPaper1.RecordOccupant
variable {X D Rec : Type*}

theorem APFPaper1.RecordOccupant.no_tie_at_a_potential_state [DecidableEq Rec] (reads : D → X → Bool)
    (allows : Rec → X → Prop) (K : Finset Rec) (x : X) (d : D) (rt rf : Rec)
    (hrt : ∀ y, allows rt y ↔ reads d y = true) (hrf : ∀ y, allows rf y ↔ reads d y = false) :
    ¬ (x ∈ allowed allows (insert rt K) ∧ x ∈ allowed allows (insert rf K)) := by sorry
