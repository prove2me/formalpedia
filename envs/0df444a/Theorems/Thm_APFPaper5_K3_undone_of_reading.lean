-- Prove2me | Theorems.Thm_APFPaper5_K3_undone_of_reading
-- name    : APFPaper5.K3.undone_of_reading
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T22:45:40.036838+00:00
-- url     : https://prove2.me/theorems/63ce8a62-202f-4487-a87b-70c8234d3b26
-- title:
--   Finite admission-invariant injective re-readings are undoable
-- statement:
--   On a finite place type, an injective reading map with MoveIsReading and AdmittedUnderReading makes every admitted move undoable from its landing place.
--
--   Publication scope: Keep hm, ha, injectivity and Finite N in their respective conclusions. Neither physical reading invariance nor identification of moves with re-readings follows from the declared inputs.
-- source:
--   ['C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/source/Theorems/Thm_APFPaper5_K3_undone_of_reading.lean:45 (source SHA256 34d43e9a2518b8c06cc7851cefb1e6dfe0a36b4f4c1a38f5f10761690020c5af; APFPaper5.K3.undone_of_reading)', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/reviews/rv2_v66_v22_review.json (SHA256 365ce42aeeada41fa76b7443fe2b5af6017c7fdeb2bb28169266b6dbba622948; modules[Theorems.Thm_APFPaper5_K3_undone_of_reading].declarations[APFPaper5.K3.undone_of_reading])']

import Definitions.Def_APFPaper5_K3_ReadingInvariance
import Theorems.Thm_APFPaper5_K3_undone_of_erases_nothing_and_goes_on
import Theorems.Thm_APFPaper5_K3_undone_of_each_kind
import Theorems.Thm_APFPaper5_K3_undoneWhereItLands_of_turnsLoseNothing
import Theorems.Thm_APFPaper5_K3_erasing_is_not_undone
import Theorems.Thm_APFPaper5_K3_one_way_is_not_undone
import Theorems.Thm_APFPaper5_K3_endless_is_not_undone

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3
universe u

theorem APFPaper5.K3.undone_of_reading {N : Type u} [Finite N] (mv : N → N → Prop) (sigma : N → N)
    (hs : Function.Injective sigma) (hm : MoveIsReading mv sigma)
    (ha : AdmittedUnderReading mv sigma) : UndoneWhereItLands mv := by sorry
