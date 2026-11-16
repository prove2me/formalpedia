-- Prove2me | Theorems.Thm_APFPaper1_Source_supportNovel_of_each_private
-- name    : APFPaper1.Source.supportNovel_of_each_private
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T22:29:29.945069+00:00
-- url     : https://prove2.me/theorems/e2a75f4d-4563-4904-90c4-64b26723a8dc
-- title:
--   Universally positive private records give novelty over every excluding family
-- statement:
--   Under additive bills, maintained=kept, necessary supports, exact service of every finite family and a positive private record for every distinction, any d outside S is support-novel over S.
--
--   Publication scope: Expose hbill, hkept, hneed, family-specific havail/havail-prime, hpos/private hypotheses, and hsuff only where used. Universal positive private records are not established and would exclude shared coarse records. Exact availability is stronger than infimal cost and is not generally granted by the paper.
-- source:
--   ['C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/source/Theorems/Thm_APFPaper1_supportNovel_of_private_record.lean:187 (source SHA256 19ca518a3d05b0ad6bcff3c90a4bb4600a9aa864fdf505fdb566014e47efa87a; APFPaper1.Source.supportNovel_of_each_private)', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/reviews/rv2_v66_v22_review.json (SHA256 365ce42aeeada41fa76b7443fe2b5af6017c7fdeb2bb28169266b6dbba622948; modules[Theorems.Thm_APFPaper1_supportNovel_of_private_record].declarations[APFPaper1.Source.supportNovel_of_each_private])']

import Theorems.Thm_APFPaper1_Source_needed_subset_kept
import Theorems.Thm_APFPaper1_Source_card_needed_le_bill
import Theorems.Thm_APFPaper1_Source_card_needed_le_familyCost
import Theorems.Thm_APFPaper1_Source_familyCost_eq_card_of_available
import Theorems.Thm_APFPaper1_Source_join_of_available
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace APFPaper1.Source
end APFPaper1.Source
open APFPaper1.Source
variable {D P R Record : Type*} [DecidableEq Record]
  (wholeResource : P → R) (calibration : R → NNReal)
  (maintained : P → Set Record)
  (sufficient : P → Set Record → D → Prop)
  (usesToRealize : P → D → Set Record → Prop)
  (kept : P → Finset Record) (fam : D → Finset Record) (cost : Record → NNReal)

theorem APFPaper1.Source.supportNovel_of_each_private
    (hbill : ∀ p : P, (calibration (wholeResource p) : ℝ) = ∑ r ∈ kept p, (cost r : ℝ))
    (hkept : ∀ p : P, maintained p = (↑(kept p) : Set Record))
    (hneed : ∀ (p : P) (sigma : Set Record) (d : D),
      sufficient p sigma d → (↑(fam d) : Set Record) ⊆ sigma)
    (havail : ∀ S : Finset D, ∃ p : P, kept p = S.biUnion fam ∧ ∀ e ∈ S, ∃ sigma : Set Record,
      sigma ⊆ maintained p ∧ sufficient p sigma e ∧ usesToRealize p e sigma)
    (hprivate : ∀ d : D, ∃ a ∈ fam d, 0 < cost a ∧ ∀ e : D, e ≠ d → a ∉ fam e)
    (S : Finset D) (d : D) (hd : d ∉ S) :
    supportNovel wholeResource calibration maintained sufficient usesToRealize S d := by sorry
