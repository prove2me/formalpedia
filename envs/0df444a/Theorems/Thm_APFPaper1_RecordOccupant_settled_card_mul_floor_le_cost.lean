-- Prove2me | Theorems.Thm_APFPaper1_RecordOccupant_settled_card_mul_floor_le_cost
-- name    : APFPaper1.RecordOccupant.settled_card_mul_floor_le_cost
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T22:26:36.123083+00:00
-- url     : https://prove2.me/theorems/18dedf13-7f77-4348-9139-c17e47358c64
-- title:
--   A per-record floor bounds the cost of fixing atomic readings
-- statement:
--   Under the atomic-record counting hypotheses, with nonnegative eps and every kept record priced at least eps, the fixed-family cardinality times eps is at most the sum of kept-record costs.
--
--   Publication scope: Expose nonemptiness, hB02, SpeaksOnlyOf, exact relation/side-record semantics, about and hatom, and nonnegative eps with per-record floor. Do not turn the count into a general dimension bound. B07b does not by this file turn classical uncertainty into ontological absence.
-- source:
--   ['C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/source/Theorems/Thm_APFPaper1_RecordOccupant_sides.lean:191 (source SHA256 939fe95a141626054481d1b351a906318012304610276c68e02f3b08bb26c738; APFPaper1.RecordOccupant.settled_card_mul_floor_le_cost)', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/reviews/rv2_v66_v22_review.json (SHA256 365ce42aeeada41fa76b7443fe2b5af6017c7fdeb2bb28169266b6dbba622948; modules[Theorems.Thm_APFPaper1_RecordOccupant_sides].declarations[APFPaper1.RecordOccupant.settled_card_mul_floor_le_cost])']

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

theorem APFPaper1.RecordOccupant.settled_card_mul_floor_le_cost [DecidableEq D] (reads : D → X → Bool)
    (allows : Rec → X → Prop) (hB02 : APFB02.EveryCombinationHeld reads) (K : Finset Rec)
    (about : Rec → D)
    (hatom : ∀ r ∈ K, ∀ x y : X, reads (about r) x = reads (about r) y → allows r x → allows r y)
    (T : Finset D) (hT : ∀ d ∈ T, ∃ b, HasSide reads allows K d b)
    (cost : Rec → ℝ) (eps : ℝ) (heps0 : 0 ≤ eps) (heps : ∀ r ∈ K, eps ≤ cost r) :
    (T.card : ℝ) * eps ≤ ∑ r ∈ K, cost r := by sorry
