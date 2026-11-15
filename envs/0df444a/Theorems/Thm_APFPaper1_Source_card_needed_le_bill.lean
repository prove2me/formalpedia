-- Prove2me | Theorems.Thm_APFPaper1_Source_card_needed_le_bill
-- name    : APFPaper1.Source.card_needed_le_bill
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T18:02:02.756299+00:00
-- url     : https://prove2.me/theorems/3c1be2e7-eed2-473c-aa67-9f414ea0908c
-- title:
--   Required-record count bounds unit-count bills below
-- statement:
--   Assume maintained support equals the kept finite set, sufficient support contains each task’s required records, and every bill equals the cardinality of the kept set. A protocol serving S bills at least the cardinality of the union of S’s required records.
-- source:
--   Theorems/Thm_APFPaper1_familyCost_count.lean:62

import Definitions.Def_APFPaper1_FamilyCost
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Card
import Mathlib.Data.NNReal.Basic
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
  (kept : P → Finset Record) (fam : D → Finset Record)

theorem APFPaper1.Source.card_needed_le_bill
    (hbill : ∀ p : P, (calibration (wholeResource p) : ℝ) = ((kept p).card : ℝ))
    (hkept : ∀ p : P, maintained p = (↑(kept p) : Set Record))
    (hneed : ∀ (p : P) (sigma : Set Record) (d : D),
      sufficient p sigma d → (↑(fam d) : Set Record) ⊆ sigma)
    (S : Finset D) (p : P)
    (hp : ∀ d ∈ S, ∃ sigma : Set Record,
      sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma) :
    ((S.biUnion fam).card : ℝ) ≤ (calibration (wholeResource p) : ℝ) := by sorry
