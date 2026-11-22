-- Prove2me | Theorems.Thm_APFPaper5_K2_isHold_comp
-- name    : APFPaper5.K2.isHold_comp
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-22T15:43:49.621864+00:00
-- url     : https://prove2.me/theorems/f3923d83-87a6-4c53-9007-98a461358952
-- title:
--   isHold comp
-- statement:
--   Scope and conditions: Identity and composition preserve IsHold. With the complete list and every combination of readings held, a hold leaves every combination available; a rearrangement leaving all combinations available has an injective index map. Preserving the ledger additionally assumes a symmetric table and a faithful nonnegative diagonal. NothingDrawn and the reading conclusions do not supply an executable word, raw-state inverse, or physical identification of this hold predicate.
--
--   Exact source statement:
--
--   theorem isHold_comp {X : Type uX} {D : Type uD} (reads : D → X → Bool) (dist : ι → D)
--       (G : ι → ι → ℝ) (h₁ h₂ : X → X) (s₁ s₂ : Equiv.Perm ι) (f₁ f₂ : ι → Bool)
--       (hh₁ : IsHold reads dist G h₁ s₁ f₁) (hh₂ : IsHold reads dist G h₂ s₂ f₂) :
--       IsHold reads dist G (h₂ ∘ h₁) (s₂.trans s₁) (fun i => xor (f₂ i) (f₁ (s₂ i)))
--
--   Source parameters:
--
--   universe uI uX uD
--   variable {ι : Type uI}
--   variable [Fintype ι]
-- source:
--   ['Theorems.Thm_APFPaper5_K2_hold_as_defined:164; USB pullbacks v58 batch B; SHA-256 6e82637a94bacb0c916dc97d59cf5372b7d8e3e65518f925ad3b71d60d94e855']

import Definitions.Def_APFPaper5_K2_Hold
import Definitions.Def_APFB02_EachTakesBothSides
import Definitions.Def_APFB02_HoldOnDistinctions
import Theorems.Thm_APFPaper5_K2_rearrangesFamily_id
import Theorems.Thm_APFPaper5_K2_rearrangesFamily_comp
import Theorems.Thm_APFPaper5_K2_nothingDrawn_of_rearranges
import Theorems.Thm_APFPaper5_K2_exists_rearranges_of_nothingDrawn
import Theorems.Thm_APFPaper5_K2_heldAfter_id
import Theorems.Thm_APFPaper5_K2_heldAfter_comp
import Theorems.Thm_APFPaper5_K2_heldAfter_add
import Theorems.Thm_APFPaper5_K2_heldAfter_smul
import Theorems.Thm_APFPaper5_K2_heldAfter_markClass
import Theorems.Thm_APFPaper5_K2_holdScore_id
import Theorems.Thm_APFPaper5_K2_holdScore_marks
import Theorems.Thm_APFPaper5_K2_holdScore_isBilinear
import Theorems.Thm_APFPaper5_K2_holdScore_eq_sum
import Theorems.Thm_APFPaper5_K2_reverse_is_inverse_of_keeps
import Theorems.Thm_APFPaper5_K2_keeps_of_reverse_is_inverse
import Theorems.Thm_APFPaper5_K2_reverse_is_inverse_iff_keeps
import Theorems.Thm_APFPaper5_K2_tableForm_heldAfter_of_keeps
import Theorems.Thm_APFPaper5_K2_ends_reversed_of_keeps
import Theorems.Thm_APFPaper5_K2_keepsTable_diag
import Theorems.Thm_APFPaper5_K2_not_keepsTable_of_diag_ne
import Theorems.Thm_APFPaper5_K2_holdScoreNull_iff_tables
import Theorems.Thm_APFPaper5_K2_source_hold_score_marks
import Theorems.Thm_APFPaper5_K2_source_hold_ends_reversed
import Definitions.Def_APFPaper5_K2_holds_keep_table_Vocabulary
import Theorems.Thm_APFPaper5_K2_keepsTable_id
import Theorems.Thm_APFPaper5_K2_keepsTable_comp
import Theorems.Thm_APFPaper5_K2_keepsTable_symm
import Theorems.Thm_APFPaper5_K2_hold_keeps_cost
import Theorems.Thm_APFPaper5_K2_holdScoreNull_before
import Theorems.Thm_APFPaper5_K2_holdScoreNull_after_of_keeps
import Theorems.Thm_APFPaper5_K2_holdScoreNull_reverse_of_keeps
import Theorems.Thm_APFPaper5_K2_hold_keeping_table_package
import Theorems.Thm_APFPaper5_K2_source_counted_hold_package
import Mathlib.Data.Finset.Image
import Mathlib.Tactic.Linarith
set_option autoImplicit false
universe apfNative_uI apfNative_uX apfNative_uD

theorem APFPaper5.K2.isHold_comp :
∀ {ι : Type apfNative_uI} {X : Type apfNative_uX} {D : Type apfNative_uD} (reads : D → X → Bool) (dist : ι → D)
  (G : ι → ι → Real) (h₁ h₂ : X → X) (s₁ s₂ : Equiv.Perm.{apfNative_uI + 1} ι) (f₁ f₂ : ι → Bool)
  (hh₁ : @APFPaper5.K2.IsHold.{apfNative_uI, apfNative_uX, apfNative_uD} ι X D reads dist G h₁ s₁ f₁)
  (hh₂ : @APFPaper5.K2.IsHold.{apfNative_uI, apfNative_uX, apfNative_uD} ι X D reads dist G h₂ s₂ f₂),
  @APFPaper5.K2.IsHold.{apfNative_uI, apfNative_uX, apfNative_uD} ι X D reads dist G
    (@Function.comp.{apfNative_uX + 1, apfNative_uX + 1, apfNative_uX + 1} X X X h₂ h₁)
    (@Equiv.trans.{apfNative_uI + 1, apfNative_uI + 1, apfNative_uI + 1} ι ι ι s₂ s₁) fun (i : ι) =>
    Bool.xor (f₂ i)
      (f₁
        (@DFunLike.coe.{apfNative_uI + 1, apfNative_uI + 1, apfNative_uI + 1} (Equiv.Perm.{apfNative_uI + 1} ι) ι
          (fun (x : ι) => ι)
          (@EquivLike.toFunLike.{apfNative_uI + 1, apfNative_uI + 1, apfNative_uI + 1} (Equiv.Perm.{apfNative_uI + 1} ι)
            ι ι (@Equiv.instEquivLike.{apfNative_uI + 1, apfNative_uI + 1} ι ι))
          s₂ i)) := by sorry
