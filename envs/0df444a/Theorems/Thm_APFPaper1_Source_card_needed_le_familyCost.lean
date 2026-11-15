-- Prove2me | Theorems.Thm_APFPaper1_Source_card_needed_le_familyCost
-- name    : APFPaper1.Source.card_needed_le_familyCost
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T18:02:02.259203+00:00
-- url     : https://prove2.me/theorems/96be4fb8-817f-4be6-a94c-9e90e3b31e65
-- title:
--   Required-record count bounds feasible family cost below
-- statement:
--   Under the same maintained/required-record binding and unit-count bills, if S is feasible, the cardinality of its required-record union is at most its infimal family cost. Feasibility prevents an empty bill-set infimum.
-- source:
--   Theorems/Thm_APFPaper1_familyCost_count.lean:75

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

theorem APFPaper1.Source.card_needed_le_familyCost
    (hbill : ∀ p : P, (calibration (wholeResource p) : ℝ) = ((kept p).card : ℝ))
    (hkept : ∀ p : P, maintained p = (↑(kept p) : Set Record))
    (hneed : ∀ (p : P) (sigma : Set Record) (d : D),
      sufficient p sigma d → (↑(fam d) : Set Record) ⊆ sigma)
    (S : Finset D)
    (hS : familyFeasible maintained sufficient usesToRealize S) :
    ((S.biUnion fam).card : ℝ) ≤
      familyCost wholeResource calibration maintained sufficient usesToRealize S := by sorry
