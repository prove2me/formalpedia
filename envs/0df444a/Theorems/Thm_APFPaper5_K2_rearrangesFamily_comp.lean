-- Prove2me | Theorems.Thm_APFPaper5_K2_rearrangesFamily_comp
-- name    : APFPaper5.K2.rearrangesFamily_comp
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T19:50:50.694686+00:00
-- url     : https://prove2.me/theorems/71ba41cf-baf8-4763-b6a4-059c614a8752
-- title:
--   rearrangesFamily comp
-- statement:
--   Result: rearrangesFamily comp. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem rearrangesFamily_comp {X : Type uX} {D : Type uD} (reads : D → X → Bool) (dist : ι → D)
--       (h₁ h₂ : X → X) (s₁ s₂ : ι → ι) (f₁ f₂ : ι → Bool)
--       (r₁ : RearrangesFamily reads dist h₁ s₁ f₁) (r₂ : RearrangesFamily reads dist h₂ s₂ f₂) :
--       RearrangesFamily reads dist (h₂ ∘ h₁) (s₁ ∘ s₂) (fun i => xor (f₂ i) (f₁ (s₂ i)))
--   ```
--
--   Module context and limits: The score uses a supplied table and precomposition of classes; side flips do not enter it. KeepsTable is an explicit hypothesis for inverse-as-adjoint and orientation results. The later author reading adopts preservation for holds but does not remove this Lean hypothesis or amend FOUNDATION_INPUTS.
--
--   Source scope parameters:
--
--   ```lean
--   universe uI uX uD uK
--   variable {ι : Type uI}
--   variable [Fintype ι] [DecidableEq ι]
--   variable {D P R Record : Type*} {ι' : Type*} [Fintype ι'] [DecidableEq ι'] [DecidableEq D]
--     [Fintype Record]
--   ```
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper5_K2_hold_score:73; pullbacks v39; source SHA-256 6ef958f4665bf38b5d47b0b531068fdc57cee8a20b837c0e17f66f223c1413c7']

import Definitions.Def_APFPaper5_K2_HoldScore
import Definitions.Def_APFPaper5_K1_identity_exchange_Vocabulary
import Theorems.Thm_APFPaper5_K1_tableForm_markClass
import Theorems.Thm_APFPaper5_K1_table_linearizes
import Theorems.Thm_APFPaper5_K1_nondegenerate_of_faithful_identity
import Theorems.Thm_APFPaper5_K1_orientationForm_zero_of_symm
import Theorems.Thm_APFPaper5_K1_ledgerForm_eq_of_symm
import Theorems.Thm_APFPaper5_K1_sourcePartyScore_symm
import Theorems.Thm_APFPaper5_K1_source_counted_family_meets_all_of_K1_with_identity_exchange
import Theorems.Thm_APFPaper5_K1_tableForm_symm
import Theorems.Thm_APFPaper5_K1_roleExchange_respects_null
import Theorems.Thm_APFPaper5_K1_interchangeable_posDef
import Theorems.Thm_APFPaper5_K1_tableForm_isBilinear
import Theorems.Thm_APFPaper5_K1_interchangeable_marks_satisfy_K1
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.Ring
set_option autoImplicit false
universe apfNative_uI apfNative_uX apfNative_uD

theorem APFPaper5.K2.rearrangesFamily_comp :
∀ {ι : Type apfNative_uI} {X : Type apfNative_uX} {D : Type apfNative_uD} (reads : D → X → Bool) (dist : ι → D)
  (h₁ h₂ : X → X) (s₁ s₂ : ι → ι) (f₁ f₂ : ι → Bool)
  (r₁ : @APFPaper5.K2.RearrangesFamily.{apfNative_uI, apfNative_uX, apfNative_uD} ι X D reads dist h₁ s₁ f₁)
  (r₂ : @APFPaper5.K2.RearrangesFamily.{apfNative_uI, apfNative_uX, apfNative_uD} ι X D reads dist h₂ s₂ f₂),
  @APFPaper5.K2.RearrangesFamily.{apfNative_uI, apfNative_uX, apfNative_uD} ι X D reads dist
    (@Function.comp.{apfNative_uX + 1, apfNative_uX + 1, apfNative_uX + 1} X X X h₂ h₁)
    (@Function.comp.{apfNative_uI + 1, apfNative_uI + 1, apfNative_uI + 1} ι ι ι s₁ s₂) fun (i : ι) =>
    Bool.xor (f₂ i) (f₁ (s₂ i)) := by sorry
