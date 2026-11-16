-- Prove2me | Theorems.Thm_APFPaper1_RecordOccupant_hasSide_mono
-- name    : APFPaper1.RecordOccupant.hasSide_mono
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T22:21:01.861787+00:00
-- url     : https://prove2.me/theorems/0cb8ba5d-0c15-4afb-8dd5-dabae57c23c1
-- title:
--   Consistent added records preserve an already-fixed side
-- statement:
--   If K is contained in K-prime, K-prime allows some state, and K fixes d to b, then K-prime also fixes d to b.
--
--   Publication scope: Expose nonemptiness, hB02, SpeaksOnlyOf, exact relation/side-record semantics, about and hatom, and nonnegative eps with per-record floor. Do not turn the count into a general dimension bound. B07b does not by this file turn classical uncertainty into ontological absence.
-- source:
--   ['C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/source/Theorems/Thm_APFPaper1_RecordOccupant_sides.lean:80 (source SHA256 939fe95a141626054481d1b351a906318012304610276c68e02f3b08bb26c738; APFPaper1.RecordOccupant.hasSide_mono)', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/reviews/rv2_v66_v22_review.json (SHA256 365ce42aeeada41fa76b7443fe2b5af6017c7fdeb2bb28169266b6dbba622948; modules[Theorems.Thm_APFPaper1_RecordOccupant_sides].declarations[APFPaper1.RecordOccupant.hasSide_mono])']

import Definitions.Def_APFPaper1_RecordOccupant
import Definitions.Def_APFB02_EachTakesBothSides
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper1.RecordOccupant
end APFPaper1.RecordOccupant
open APFPaper1.RecordOccupant
variable {X D Rec : Type*}

theorem APFPaper1.RecordOccupant.hasSide_mono (reads : D → X → Bool) (allows : Rec → X → Prop) (K K' : Finset Rec)
    (hsub : K ⊆ K') (hne : (allowed allows K').Nonempty) (d : D) (b : Bool)
    (h : HasSide reads allows K d b) : HasSide reads allows K' d b := by sorry
