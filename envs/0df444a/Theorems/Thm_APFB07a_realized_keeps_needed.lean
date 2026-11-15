-- Prove2me | Theorems.Thm_APFB07a_realized_keeps_needed
-- name    : APFB07a.realized_keeps_needed
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T18:49:31.791375+00:00
-- url     : https://prove2.me/theorems/af82eeae-f566-4224-98e4-fdb1882fef8e
-- title:
--   Protocol-bound selection keeps every required record
-- statement:
--   Assume A2Selection on serving protocols whose bills fit C, maintained=kept, and every sufficient support contains the task’s required records. Then the protocol selected for any S keeps its entire required-record union; the service part of A2 suffices.
-- source:
--   Theorems/Thm_APFB07a_realized_keeps_needed.lean:41

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

theorem APFB07a.realized_keeps_needed
    (hA2 : APFB07a.A2Selection (Interface := Finset D) (Configuration := fun _ => P)
      (fun S p => APFB07a.protocolAdmissible wholeResource calibration maintained sufficient
        usesToRealize C S p)
      (fun _ p => APFB07a.protocolBill wholeResource calibration p) realized)
    (hkept : ∀ p : P, maintained p = (↑(kept p) : Set Record))
    (hneed : ∀ (p : P) (sigma : Set Record) (d : D),
      sufficient p sigma d → (↑(fam d) : Set Record) ⊆ sigma)
    (S : Finset D) :
    S.biUnion fam ⊆ kept (realized S) := by sorry
