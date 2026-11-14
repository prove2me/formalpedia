-- Prove2me | Theorems.Thm_APFPaper5_K1_recordModelCost_eq
-- name    : APFPaper5.K1.recordModelCost_eq
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:08:50.14805+00:00
-- url     : https://prove2.me/theorems/ae363ede-741b-438e-a1da-a57455b2951e
-- title:
--   RecordModelCost equals the total weight of required records
-- statement:
--   For nonnegative record weights w and finite required-record sets R(i), recordModelCost(w,R,S) equals the sum of w over the union of R(i) for i in the finite family S. The defined model uses finite record sets as protocols, additive weight bills, support-inclusion service and unrestricted realization. This declaration gives the exact cost formula for that model. It makes no claim that an original physical interface is a record model or that its admissible protocols include every finite record set.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_weighted_record_model.lean:55; Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex, 1772-1792;2502-2530; Artifacts_2026-11-12_session/claude/EthanBrooke-01WrrBvu/RULING_records_clause_2026-11-12.md, 1

import Definitions.Def_APFPaper5_K1_RecordModel
import Definitions.Def_APFPaper5_K1_SharedCost
import Theorems.Thm_APFPaper5_K1_atomTable_symm
import Theorems.Thm_APFPaper5_K1_atomTable_form
import Theorems.Thm_APFPaper5_K1_atomTable_nonneg
import Theorems.Thm_APFPaper5_K1_record_book_table_satisfies_K1
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open APFPaper1.Source
namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5.K1
universe u v
variable {ι : Type u} {Rec : Type v} [DecidableEq Rec]

theorem APFPaper5.K1.recordModelCost_eq (w : Rec → NNReal) (fam : ι → Finset Rec) (S : Finset ι) :
    recordModelCost w fam S = ∑ a ∈ S.biUnion fam, (w a : ℝ) := by sorry
