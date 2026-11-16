-- Prove2me | Theorems.Thm_APFB02_hold_reaches_every_state
-- name    : APFB02.hold_reaches_every_state
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T22:42:12.890207+00:00
-- url     : https://prove2.me/theorems/dc374826-d89b-416b-a40d-7d9104c24b6a
-- title:
--   Partial image coverage reaches every raw state
-- statement:
--   With finitely many readings separating raw states and StillHeldAfterOn, every target state has a preimage at which the map runs.
--
--   Publication scope: hsep identifies RAW states, stronger than equality of continuation profiles. Finite D and partial image coverage are supplied. The total function h with predicate runs is not an original execution certificate.
-- source:
--   ['C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/source/Theorems/Thm_APFB02_hold_runs_everywhere.lean:45 (source SHA256 699e887b86e91508f1740a70597685926a229336bfb32e6a293fd0826bc57e4b; APFB02.hold_reaches_every_state)', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/reviews/rv2_v66_v22_review.json (SHA256 365ce42aeeada41fa76b7443fe2b5af6017c7fdeb2bb28169266b6dbba622948; modules[Theorems.Thm_APFB02_hold_runs_everywhere].declarations[APFB02.hold_reaches_every_state])']

import Definitions.Def_APFB02_HoldWhereItRuns
import Theorems.Thm_APFPaper5_K3_undone_of_erases_nothing_and_goes_on
import Theorems.Thm_APFPaper5_K3_undone_of_each_kind
import Theorems.Thm_APFPaper5_K3_undoneWhereItLands_of_turnsLoseNothing
import Theorems.Thm_APFPaper5_K3_erasing_is_not_undone
import Theorems.Thm_APFPaper5_K3_one_way_is_not_undone
import Theorems.Thm_APFPaper5_K3_endless_is_not_undone
import Mathlib.Data.Fintype.Pi

set_option autoImplicit false
open APFPaper5.K3

namespace APFB02
end APFB02
open APFB02

theorem APFB02.hold_reaches_every_state {X D : Type*} [Fintype D] (reads : D → X → Bool)
    (runs : X → Prop) (h : X → X)
    (hsep : ∀ x y : X, (∀ d : D, reads d x = reads d y) → x = y)
    (h2 : StillHeldAfterOn reads runs h) (y : X) : ∃ x : X, runs x ∧ h x = y := by sorry
