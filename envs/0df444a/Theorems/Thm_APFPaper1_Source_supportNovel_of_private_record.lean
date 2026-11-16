-- Prove2me | Theorems.Thm_APFPaper1_Source_supportNovel_of_private_record
-- name    : APFPaper1.Source.supportNovel_of_private_record
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T22:29:28.225123+00:00
-- url     : https://prove2.me/theorems/842c6948-d222-497a-bab6-08d1d4c9f871
-- title:
--   A positive private record gives support novelty under exact service
-- statement:
--   Under the bill, kept and necessary-support hypotheses and exact service of S, a positive-cost record needed by d but outside S's required-record union makes d support-novel over S.
--
--   Publication scope: Expose hbill, hkept, hneed, family-specific havail/havail-prime, hpos/private hypotheses, and hsuff only where used. Universal positive private records are not established and would exclude shared coarse records. Exact availability is stronger than infimal cost and is not generally granted by the paper.
-- source:
--   ['C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/source/Theorems/Thm_APFPaper1_supportNovel_of_private_record.lean:99 (source SHA256 19ca518a3d05b0ad6bcff3c90a4bb4600a9aa864fdf505fdb566014e47efa87a; APFPaper1.Source.supportNovel_of_private_record)', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/reviews/rv2_v66_v22_review.json (SHA256 365ce42aeeada41fa76b7443fe2b5af6017c7fdeb2bb28169266b6dbba622948; modules[Theorems.Thm_APFPaper1_supportNovel_of_private_record].declarations[APFPaper1.Source.supportNovel_of_private_record])']

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

theorem APFPaper1.Source.supportNovel_of_private_record
    (hbill : ∀ p : P, (calibration (wholeResource p) : ℝ) = ∑ r ∈ kept p, (cost r : ℝ))
    (hkept : ∀ p : P, maintained p = (↑(kept p) : Set Record))
    (hneed : ∀ (p : P) (sigma : Set Record) (d : D),
      sufficient p sigma d → (↑(fam d) : Set Record) ⊆ sigma)
    (S : Finset D) (d : D)
    (havail : ∃ p : P, kept p = S.biUnion fam ∧ ∀ e ∈ S, ∃ sigma : Set Record,
      sigma ⊆ maintained p ∧ sufficient p sigma e ∧ usesToRealize p e sigma)
    (a : Record) (had : a ∈ fam d) (haS : a ∉ S.biUnion fam) (hpos : 0 < cost a) :
    supportNovel wholeResource calibration maintained sufficient usesToRealize S d := by sorry
