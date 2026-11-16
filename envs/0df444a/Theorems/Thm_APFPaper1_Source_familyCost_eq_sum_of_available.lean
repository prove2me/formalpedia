-- Prove2me | Theorems.Thm_APFPaper1_Source_familyCost_eq_sum_of_available
-- name    : APFPaper1.Source.familyCost_eq_sum_of_available
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T22:28:23.98514+00:00
-- url     : https://prove2.me/theorems/68f9b64b-c897-488f-8de2-dfb665f9c6b1
-- title:
--   Exact service identifies family cost with the required-record sum
-- statement:
--   Under additive bills, maintained=kept and necessary supports, a protocol serving S while keeping exactly S's required-record union makes familyCost(S) equal the sum over that union.
--
--   Publication scope: Expose hbill, hkept, hneed, family-specific havail/havail-prime, hpos/private hypotheses, and hsuff only where used. Universal positive private records are not established and would exclude shared coarse records. Exact availability is stronger than infimal cost and is not generally granted by the paper.
-- source:
--   ['C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/source/Theorems/Thm_APFPaper1_supportNovel_of_private_record.lean:75 (source SHA256 19ca518a3d05b0ad6bcff3c90a4bb4600a9aa864fdf505fdb566014e47efa87a; APFPaper1.Source.familyCost_eq_sum_of_available)', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/reviews/rv2_v66_v22_review.json (SHA256 365ce42aeeada41fa76b7443fe2b5af6017c7fdeb2bb28169266b6dbba622948; modules[Theorems.Thm_APFPaper1_supportNovel_of_private_record].declarations[APFPaper1.Source.familyCost_eq_sum_of_available])']

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

theorem APFPaper1.Source.familyCost_eq_sum_of_available
    (hbill : ∀ p : P, (calibration (wholeResource p) : ℝ) = ∑ r ∈ kept p, (cost r : ℝ))
    (hkept : ∀ p : P, maintained p = (↑(kept p) : Set Record))
    (hneed : ∀ (p : P) (sigma : Set Record) (d : D),
      sufficient p sigma d → (↑(fam d) : Set Record) ⊆ sigma)
    (S : Finset D)
    (havail : ∃ p : P, kept p = S.biUnion fam ∧ ∀ d ∈ S, ∃ sigma : Set Record,
      sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma) :
    familyCost wholeResource calibration maintained sufficient usesToRealize S =
      ∑ r ∈ S.biUnion fam, (cost r : ℝ) := by sorry
