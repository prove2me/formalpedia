-- Prove2me | Theorems.Thm_APFPaper5_K1_recordModel_satisfies_K1
-- name    : APFPaper5.K1.recordModel_satisfies_K1
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:09:02.961845+00:00
-- url     : https://prove2.me/theorems/8930401a-7e3b-4d6a-8dcb-7dda1960a3b1
-- title:
--   Positive private records give the model’s shared-cost form a faithful diagonal
-- statement:
--   Let record and family-index types be finite. Supply nonnegative record weights w and finite required-record sets R(i). Assume hprivate: every family has a record of positive weight that belongs to that family and to no other listed family. The table whose entries are sharedCost(recordModelCost,{i},{j}) defines a real-bilinear coefficient form with a faithful nonnegative diagonal under identity role exchange. These are the displayed algebraic K1 predicates for the supplied model. No physical RECORDS realization or completion of the physical K1 obligation is asserted.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_weighted_record_model.lean:88; Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex, 1772-1792;2502-2530; Artifacts_2026-11-12_session/claude/EthanBrooke-01WrrBvu/RULING_records_clause_2026-11-12.md, 1

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

theorem APFPaper5.K1.recordModel_satisfies_K1 [Fintype Rec] [Fintype ι] [DecidableEq ι] (w : Rec → NNReal)
    (fam : ι → Finset Rec) (hprivate : ∀ i, ∃ a, 0 < w a ∧ ∀ j, (a ∈ fam j ↔ j = i)) :
    IsBilinear (VP := ι → ℝ) (VE := ι → ℝ)
        (tableForm (fun i j => sharedCost (recordModelCost w fam) {i} {j})) ∧
      FaithfulNonnegDiagonal (tableForm (fun i j => sharedCost (recordModelCost w fam) {i} {j}))
        (LinearEquiv.refl ℝ (ι → ℝ)) := by sorry
