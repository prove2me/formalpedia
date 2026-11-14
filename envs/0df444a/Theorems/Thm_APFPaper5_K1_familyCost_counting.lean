-- Prove2me | Theorems.Thm_APFPaper5_K1_familyCost_counting
-- name    : APFPaper5.K1.familyCost_counting
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:52:12.454129+00:00
-- url     : https://prove2.me/theorems/10999f1d-2a2f-4098-a246-c17f1236a2fe
-- title:
--   The finite-record counting model has union-cardinality family cost
-- statement:
--   Assign each distinction d a finite set R(d) of required records. In the supplied model, protocols are all finite record sets, a protocol serves d when it contains R(d), the realization predicate is always true, and its bill is its number of records. For any finite family S, the familyCost infimum equals the cardinality of the union of R(d) over d in S. The union provides an attaining protocol within this model. The theorem does not identify arbitrary physical execution or costs with this counting construction.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_shared_cost_counting.lean:34; Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex, 1772-1792;2502-2530; Artifacts_2026-11-12_session/claude/EthanBrooke-01WrrBvu/RULING_two_adoptions_2026-11-12.md, 1

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

theorem APFPaper5.K1.familyCost_counting (fam : ι → Finset Rec) (S : Finset ι) :
    familyCost (D := ι) (P := Finset Rec) (R := Finset Rec) (Record := Rec)
      (fun p => p) (fun r => (r.card : NNReal)) (fun p => (↑p : Set Rec))
      (fun _ sigma d => (↑(fam d) : Set Rec) ⊆ sigma) (fun _ _ _ => True) S =
      ((S.biUnion fam).card : ℝ) := by sorry
