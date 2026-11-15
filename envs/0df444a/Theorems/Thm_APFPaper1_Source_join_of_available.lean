-- Prove2me | Theorems.Thm_APFPaper1_Source_join_of_available
-- name    : APFPaper1.Source.join_of_available
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T18:13:33.026243+00:00
-- url     : https://prove2.me/theorems/ba7b7508-c94c-4ba6-bf39-fccccb08be3e
-- title:
--   Exact-serving availability supplies a joint protocol within the sum of bills
-- statement:
--   Under unit-count bills, maintained=kept and required-record containment, suppose a protocol serves S union T while keeping exactly its required-record union. For any p serving S and q serving T, some protocol serves their union with bill at most bill(p)+bill(q). No separate numerical capacity conclusion is asserted.
-- source:
--   Theorems/Thm_APFPaper1_familyCost_count.lean:110

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

theorem APFPaper1.Source.join_of_available [DecidableEq D]
    (hbill : ∀ p : P, (calibration (wholeResource p) : ℝ) = ((kept p).card : ℝ))
    (hkept : ∀ p : P, maintained p = (↑(kept p) : Set Record))
    (hneed : ∀ (p : P) (sigma : Set Record) (d : D),
      sufficient p sigma d → (↑(fam d) : Set Record) ⊆ sigma)
    (S T : Finset D)
    (havail : ∃ p : P, kept p = (S ∪ T).biUnion fam ∧ ∀ d ∈ S ∪ T, ∃ sigma : Set Record,
      sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma)
    (p q : P)
    (hp : ∀ d ∈ S, ∃ sigma : Set Record,
      sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma)
    (hq : ∀ d ∈ T, ∃ sigma : Set Record,
      sigma ⊆ maintained q ∧ sufficient q sigma d ∧ usesToRealize q d sigma) :
    ∃ pq : P,
      (∀ d ∈ S ∪ T, ∃ sigma : Set Record,
        sigma ⊆ maintained pq ∧ sufficient pq sigma d ∧ usesToRealize pq d sigma) ∧
      (calibration (wholeResource pq) : ℝ) ≤
        (calibration (wholeResource p) : ℝ) + (calibration (wholeResource q) : ℝ) := by sorry
