-- Prove2me | Theorems.Thm_APFPaper5_K3_erasing_is_not_undone
-- name    : APFPaper5.K3.erasing_is_not_undone
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T22:33:09.523201+00:00
-- url     : https://prove2.me/theorems/8c76cec9-7faa-44b7-8cae-ef76d95c3a1d
-- title:
--   A finite erasing relation need not be undoable
-- statement:
--   The Boolean relation sending every source to true has one outcome and can continue, but is not undoable from every landing place.
--
--   Publication scope: State all four requirements: finite places plus the three predicates. The counterexamples are small relations, not worlds of all eight inputs; they do not establish necessity of every possible formulation or physical irreversibility.
-- source:
--   ['C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/source/Theorems/Thm_APFPaper5_K3_undone_where_it_lands.lean:83 (source SHA256 637e4a340c6b6ce0d84cf7cf0f24a0ee0693c8ea1f323cca1acce15bff8bc104; APFPaper5.K3.erasing_is_not_undone)', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/reviews/rv2_v66_v22_review.json (SHA256 365ce42aeeada41fa76b7443fe2b5af6017c7fdeb2bb28169266b6dbba622948; modules[Theorems.Thm_APFPaper5_K3_undone_where_it_lands].declarations[APFPaper5.K3.erasing_is_not_undone])']

import Definitions.Def_APFPaper5_K3_UndoneWhereItLands
import Definitions.Def_APFPaper5_K3_Continuity
import Theorems.Thm_APFPaper5_K3_undo_is_a_repeat
import Theorems.Thm_APFPaper5_K3_kept_along_the_hold
import Theorems.Thm_APFPaper5_K3_every_state_comes_to_return
import Theorems.Thm_APFPaper5_K3_occupant_settles
import Theorems.Thm_APFPaper5_K3_finite_of_separating_family
import Theorems.Thm_APFB01_every_object_comes_to_return

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3
universe u

theorem APFPaper5.K3.erasing_is_not_undone :
    OneOutcome (fun _ v : Bool => v = true) ∧ GoesOn (fun _ v : Bool => v = true) ∧
      ¬ UndoneWhereItLands (fun _ v : Bool => v = true) := by sorry
