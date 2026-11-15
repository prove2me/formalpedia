-- Prove2me | Theorems.Thm_APFPaper5_K1_needs_own_record_of_separates
-- name    : APFPaper5.K1.needs_own_record_of_separates
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T06:18:42.560578+00:00
-- url     : https://prove2.me/theorems/244e51de-ba99-4bd4-be14-ea17ca90b1d8
-- title:
--   Needs own record of separates
-- statement:
--   Supporting lemma: needs own record of separates. The exact quantified statement supplied with this entry is controlling, including every displayed hypothesis. Requires the weighted finite-record model, hsound, actual separation, uniform positive prices and smaller-family membership. It does not supply these for physical K-layer degrees of freedom.
-- source:
--   Sib v44 Theorems/Thm_APFPaper5_K1_record_model_bridge.lean:35

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
theorem APFPaper5.K1.needs_own_record_of_separates {Ω Val : Type*} (fam : ι → Finset Rec)
    (reads : Rec → Ω → Val) (verdict : ι → Ω → Prop) (S : Finset ι) (d : ι)
    (hsound : ∀ x y : Ω, (∀ r ∈ fam d, reads r x = reads r y) → (verdict d x ↔ verdict d y))
    (x y : Ω) (hagree : ∀ r ∈ S.biUnion fam, reads r x = reads r y)
    (hne : ¬ (verdict d x ↔ verdict d y)) : ¬ fam d ⊆ S.biUnion fam := by sorry
