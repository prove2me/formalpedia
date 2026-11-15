-- Prove2me | Theorems.Thm_APFB07a_realized_keeps_exactly_needed
-- name    : APFB07a.realized_keeps_exactly_needed
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T18:47:06.804962+00:00
-- url     : https://prove2.me/theorems/48ddb6cc-1dc1-4f81-80a4-8882e7da34a0
-- title:
--   Unit billing and availability make selection keep exactly the required records
-- statement:
--   Assume protocol-bound A2Selection, maintained=kept, required-record containment and unit-count bills. If a protocol serving S keeps exactly its required-record union, the selected protocol also keeps exactly that union. The availability and billing conditions are explicit.
-- source:
--   Theorems/Thm_APFB07a_realized_keeps_needed.lean:54

import Theorems.Thm_APFB07a_familyCost_attained_of_A2
import Theorems.Thm_APFB07b_realized_protocol_unique_at_its_bill
import Theorems.Thm_APFPaper1_Source_needed_subset_kept
import Theorems.Thm_APFPaper1_Source_card_needed_le_bill
import Theorems.Thm_APFPaper1_Source_card_needed_le_familyCost
import Theorems.Thm_APFPaper1_Source_familyCost_eq_card_of_available
import Theorems.Thm_APFPaper1_Source_join_of_available

set_option autoImplicit false
open APFPaper1.Source


variable {D P R Record : Type*} [DecidableEq Record]
  (wholeResource : P → R) (calibration : R → NNReal)
  (maintained : P → Set Record)
  (sufficient : P → Set Record → D → Prop)
  (usesToRealize : P → D → Set Record → Prop)
  (kept : P → Finset Record) (fam : D → Finset Record)
  (C : ℝ) (realized : Finset D → P)

theorem APFB07a.realized_keeps_exactly_needed
    (hA2 : APFB07a.A2Selection (Interface := Finset D) (Configuration := fun _ => P)
      (fun S p => APFB07a.protocolAdmissible wholeResource calibration maintained sufficient
        usesToRealize C S p)
      (fun _ p => APFB07a.protocolBill wholeResource calibration p) realized)
    (hbill : ∀ p : P, (calibration (wholeResource p) : ℝ) = ((kept p).card : ℝ))
    (hkept : ∀ p : P, maintained p = (↑(kept p) : Set Record))
    (hneed : ∀ (p : P) (sigma : Set Record) (d : D),
      sufficient p sigma d → (↑(fam d) : Set Record) ⊆ sigma)
    (S : Finset D)
    (havail : ∃ p : P, kept p = S.biUnion fam ∧ ∀ d ∈ S, ∃ sigma : Set Record,
      sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma) :
    kept (realized S) = S.biUnion fam := by sorry
