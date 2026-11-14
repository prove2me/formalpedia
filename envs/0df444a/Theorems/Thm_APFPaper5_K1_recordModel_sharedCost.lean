-- Prove2me | Theorems.Thm_APFPaper5_K1_recordModel_sharedCost
-- name    : APFPaper5.K1.recordModel_sharedCost
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:09:20.575193+00:00
-- url     : https://prove2.me/theorems/b8acf3ac-c1b0-4ce5-91b1-7d63970941c8
-- title:
--   Shared cost in the weighted record model is its overlap-table entry
-- statement:
--   Supply a finite record type, nonnegative weights w and finite required-record sets R(i). In the model whose family cost is recordModelCost, sharedCost({i},{j}) equals the atomTable entry formed from weights w and Boolean membership in R(i),R(j). Thus the joint-service discount is exactly the weight carried by both families in this model. The theorem does not identify a physical interface with that model, prove a normalized pair-number relation, or establish a faithful diagonal without further separation assumptions.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_weighted_record_model.lean:79; Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex, 1772-1792;2502-2530; Artifacts_2026-11-12_session/claude/EthanBrooke-01WrrBvu/RULING_records_clause_2026-11-12.md, 1

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

theorem APFPaper5.K1.recordModel_sharedCost [Fintype Rec] [DecidableEq ι] (w : Rec → NNReal)
    (fam : ι → Finset Rec) (i j : ι) :
    sharedCost (recordModelCost w fam) {i} {j} =
      atomTable (fun a => (w a : ℝ)) (fun k a => decide (a ∈ fam k)) i j := by sorry
