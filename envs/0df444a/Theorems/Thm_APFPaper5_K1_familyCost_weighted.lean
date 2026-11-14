-- Prove2me | Theorems.Thm_APFPaper5_K1_familyCost_weighted
-- name    : APFPaper5.K1.familyCost_weighted
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:08:24.236069+00:00
-- url     : https://prove2.me/theorems/b693f920-ee07-4af6-a512-a662ed92df04
-- title:
--   Weighted finite-record protocols have union-weight family cost
-- statement:
--   Assign each distinction d a finite set R(d) of required records and each record a nonnegative real weight. Protocols are all finite record sets, the bill is the sum of their weights, service is containment of the required records, and realization is unrestricted. For every finite family S, the familyCost infimum equals the total weight of the union of R(d) over d∈S. This is an attained infimum in the supplied model, not a proof that arbitrary physical protocol costs obey additive record accounting.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_weighted_record_model.lean:32; Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex, 1772-1792;2502-2530; Artifacts_2026-11-12_session/claude/EthanBrooke-01WrrBvu/RULING_records_clause_2026-11-12.md, 1

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

theorem APFPaper5.K1.familyCost_weighted (w : Rec → NNReal) (fam : ι → Finset Rec) (S : Finset ι) :
    familyCost (D := ι) (P := Finset Rec) (R := Finset Rec) (Record := Rec)
      (fun p => p) (fun r => ∑ a ∈ r, w a) (fun p => (↑p : Set Rec))
      (fun _ sigma d => (↑(fam d) : Set Rec) ⊆ sigma) (fun _ _ _ => True) S =
      ∑ a ∈ S.biUnion fam, (w a : ℝ) := by sorry
