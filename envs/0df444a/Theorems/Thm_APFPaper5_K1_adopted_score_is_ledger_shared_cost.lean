-- Prove2me | Theorems.Thm_APFPaper5_K1_adopted_score_is_ledger_shared_cost
-- name    : APFPaper5.K1.adopted_score_is_ledger_shared_cost
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:50:29.282205+00:00
-- url     : https://prove2.me/theorems/ac71e8b1-41be-475f-a3b0-1fea63f19624
-- title:
--   The counting record model’s shared family cost equals the chosen count score
-- statement:
--   Supply a finite record type and finite required-record sets R(i). Use the familyCost model whose protocols are finite record sets, bills are record counts, service means containing the required records, and realization is unrestricted. Its sharedCost on singleton index families {i} and {j} equals sharedTable(R,i,j). This connects the author-chosen record-side score to this explicit counting instance of familyCost. It does not establish that an original physical interface realizes the model or that its general ordered score is this count.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_shared_cost_counting.lean:64; Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex, 1772-1792;2502-2530; Artifacts_2026-11-12_session/claude/EthanBrooke-01WrrBvu/RULING_two_adoptions_2026-11-12.md, 1

import Definitions.Def_APFPaper1_FamilyCost
import Definitions.Def_APFPaper5_K1_SharedCost
import Theorems.Thm_APFPaper5_K1_sharedTable_eq_card
import Theorems.Thm_APFPaper5_K1_sharedCost_self
import Theorems.Thm_APFPaper5_K1_sharedCost_le_right
import Theorems.Thm_APFPaper5_K1_sharedCost_le_left
import Theorems.Thm_APFPaper5_K1_sharedCost_nonneg_iff
import Theorems.Thm_APFPaper5_K1_sharedCost_channel_ledger
import Theorems.Thm_APFPaper5_K1_sharedCost_channel_no_joint
import Theorems.Thm_APFPaper5_K1_cost_is_count_times_floor
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open APFPaper1.Source
namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5.K1
universe u v w
variable {ι : Type u} {Rec : Type v} [DecidableEq Rec]

theorem APFPaper5.K1.adopted_score_is_ledger_shared_cost [Fintype Rec] [DecidableEq ι] (fam : ι → Finset Rec)
    (i j : ι) :
    sharedCost (familyCost (D := ι) (P := Finset Rec) (R := Finset Rec) (Record := Rec)
      (fun p => p) (fun r => (r.card : NNReal)) (fun p => (↑p : Set Rec))
      (fun _ sigma d => (↑(fam d) : Set Rec) ⊆ sigma) (fun _ _ _ => True)) {i} {j} =
      sharedTable fam i j := by sorry
