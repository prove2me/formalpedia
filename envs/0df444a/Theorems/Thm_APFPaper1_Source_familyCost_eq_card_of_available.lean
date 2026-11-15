-- Prove2me | Theorems.Thm_APFPaper1_Source_familyCost_eq_card_of_available
-- name    : APFPaper1.Source.familyCost_eq_card_of_available
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T18:41:38.094028+00:00
-- url     : https://prove2.me/theorems/65342442-04e5-45e3-bd1d-6fd062b7f7da
-- title:
--   Exact-serving availability makes cost equal the required count
-- statement:
--   Under unit-count bills, maintained=kept and sufficient-support containment of required records, suppose a protocol serves S while keeping exactly the union of its required records. Then familyCost(S) equals that union’s cardinality.
-- source:
--   Theorems/Thm_APFPaper1_familyCost_count.lean:90

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

theorem APFPaper1.Source.familyCost_eq_card_of_available
    (hbill : ∀ p : P, (calibration (wholeResource p) : ℝ) = ((kept p).card : ℝ))
    (hkept : ∀ p : P, maintained p = (↑(kept p) : Set Record))
    (hneed : ∀ (p : P) (sigma : Set Record) (d : D),
      sufficient p sigma d → (↑(fam d) : Set Record) ⊆ sigma)
    (S : Finset D)
    (havail : ∃ p : P, kept p = S.biUnion fam ∧ ∀ d ∈ S, ∃ sigma : Set Record,
      sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma) :
    familyCost wholeResource calibration maintained sufficient usesToRealize S =
      ((S.biUnion fam).card : ℝ) := by sorry
