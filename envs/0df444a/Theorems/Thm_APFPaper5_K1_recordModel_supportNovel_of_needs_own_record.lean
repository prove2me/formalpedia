-- Prove2me | Theorems.Thm_APFPaper5_K1_recordModel_supportNovel_of_needs_own_record
-- name    : APFPaper5.K1.recordModel_supportNovel_of_needs_own_record
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T06:27:42.019055+00:00
-- url     : https://prove2.me/theorems/550b8ddd-6c16-428f-9894-3f3c95666ccf
-- title:
--   Recordmodel supportnovel of needs own record
-- statement:
--   In the weighted finite-record model, suppose every record has price at least positive epsilon and d requires a record outside the union required by S. Then d is support-novel over S in the shared family-cost definition; the proof uses a near-optimal window epsilon/2.
-- source:
--   Sib v44 Theorems/Thm_APFPaper5_K1_record_model_bridge.lean:43

import Definitions.Def_APFPaper5_K1_RecordModel
import Theorems.Thm_APFPaper5_K1_familyCost_weighted
import Theorems.Thm_APFPaper5_K1_recordModelCost_eq
import Theorems.Thm_APFPaper5_K1_recordModel_sharedCost
import Theorems.Thm_APFPaper5_K1_recordModel_satisfies_K1
import Theorems.Thm_APFPaper5_K1_recordModel_economy
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open APFPaper1.Source
namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5.K1
universe u v
variable {ι : Type u} {Rec : Type v} [DecidableEq Rec] [DecidableEq ι]

omit [DecidableEq ι] in
theorem APFPaper5.K1.recordModel_supportNovel_of_needs_own_record (w : Rec → NNReal) (fam : ι → Finset Rec)
    (eps : ℝ) (heps : 0 < eps) (hw : ∀ a, eps ≤ (w a : ℝ)) (S : Finset ι) (d : ι)
    (hneeds : ¬ fam d ⊆ S.biUnion fam) :
    supportNovel (D := ι) (P := Finset Rec) (R := Finset Rec) (Record := Rec)
      (fun p => p) (fun r => ∑ a ∈ r, w a) (fun p => (↑p : Set Rec))
      (fun _ sigma e => (↑(fam e) : Set Rec) ⊆ sigma) (fun _ _ _ => True) S d := by sorry
