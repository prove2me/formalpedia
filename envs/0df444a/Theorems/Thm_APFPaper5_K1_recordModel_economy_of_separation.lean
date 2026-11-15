-- Prove2me | Theorems.Thm_APFPaper5_K1_recordModel_economy_of_separation
-- name    : APFPaper5.K1.recordModel_economy_of_separation
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T06:26:39.676641+00:00
-- url     : https://prove2.me/theorems/da53ea09-58ed-47fe-bf1d-81ba84e9e19b
-- title:
--   Recordmodel economy of separation
-- statement:
--   In the weighted finite-record model with a uniform positive price floor, suppose d’s required records determine its verdict and two states agree on the records of S but differ on d. If actual minimizes modeled family cost over a supplied set containing S, actual is not insert d S. No original physical A2 or private-record requirement is inferred.
-- source:
--   Sib v44 Theorems/Thm_APFPaper5_K1_record_model_bridge.lean:69

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

theorem APFPaper5.K1.recordModel_economy_of_separation {Ω Val : Type*} (w : Rec → NNReal)
    (fam : ι → Finset Rec) (eps : ℝ) (heps : 0 < eps) (hw : ∀ a, eps ≤ (w a : ℝ))
    (reads : Rec → Ω → Val) (verdict : ι → Ω → Prop) (families : Set (Finset ι))
    (actual : Finset ι)
    (hA2 : actual ∈ families ∧
      ∀ a ∈ families, recordModelCost w fam actual ≤ recordModelCost w fam a)
    (S : Finset ι) (d : ι) (hSmem : S ∈ families)
    (hsound : ∀ x y : Ω, (∀ r ∈ fam d, reads r x = reads r y) → (verdict d x ↔ verdict d y))
    (x y : Ω) (hagree : ∀ r ∈ S.biUnion fam, reads r x = reads r y)
    (hne : ¬ (verdict d x ↔ verdict d y)) : actual ≠ insert d S := by sorry
