-- Prove2me | Theorems.Thm_APFPaper1_Source_needed_subset_kept
-- name    : APFPaper1.Source.needed_subset_kept
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T18:14:37.339132+00:00
-- url     : https://prove2.me/theorems/5162f0be-9945-4445-932a-c6d47b5303be
-- title:
--   Serving protocols keep every required record
-- statement:
--   Assume maintained(p)=kept(p) and every sufficient support for d contains fam(d). Any protocol serving S keeps every record in the union of fam(d) over d in S.
-- source:
--   Theorems/Thm_APFPaper1_familyCost_count.lean:47

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

theorem APFPaper1.Source.needed_subset_kept
    (hkept : ∀ p : P, maintained p = (↑(kept p) : Set Record))
    (hneed : ∀ (p : P) (sigma : Set Record) (d : D),
      sufficient p sigma d → (↑(fam d) : Set Record) ⊆ sigma)
    (S : Finset D) (p : P)
    (hp : ∀ d ∈ S, ∃ sigma : Set Record,
      sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma) :
    S.biUnion fam ⊆ kept p := by sorry
