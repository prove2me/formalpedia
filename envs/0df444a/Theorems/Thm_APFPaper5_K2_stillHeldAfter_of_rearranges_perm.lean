-- Prove2me | Theorems.Thm_APFPaper5_K2_stillHeldAfter_of_rearranges_perm
-- name    : APFPaper5.K2.stillHeldAfter_of_rearranges_perm
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-22T16:06:21.07696+00:00
-- url     : https://prove2.me/theorems/52a4914a-bced-4d71-9a40-0e00b69056f6
-- title:
--   stillHeldAfter of rearranges perm
-- statement:
--   Scope and conditions: Identity and composition preserve IsHold. With the complete list and every combination of readings held, a hold leaves every combination available; a rearrangement leaving all combinations available has an injective index map. Preserving the ledger additionally assumes a symmetric table and a faithful nonnegative diagonal. NothingDrawn and the reading conclusions do not supply an executable word, raw-state inverse, or physical identification of this hold predicate.
--
--   Exact source statement:
--
--   theorem stillHeldAfter_of_rearranges_perm {X : Type uX} {D : Type uD} (reads : D → X → Bool)
--       (h : X → X) (sigma : Equiv.Perm D) (flip : D → Bool)
--       (r : RearrangesFamily reads id h (sigma : D → D) flip)
--       (hall : APFB02.EveryCombinationHeld reads) : APFB02.StillHeldAfter reads h
--
--   Source parameters:
--
--   universe uI uX uD
--   variable {ι : Type uI}
--   variable [Fintype ι]
-- source:
--   ['Theorems.Thm_APFPaper5_K2_hold_as_defined:180; USB pullbacks v58 batch B; SHA-256 6e82637a94bacb0c916dc97d59cf5372b7d8e3e65518f925ad3b71d60d94e855']

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
universe apfNative_uX apfNative_uD

theorem APFPaper5.K2.stillHeldAfter_of_rearranges_perm :
∀ {X : Type apfNative_uX} {D : Type apfNative_uD} (reads : D → X → Bool) (h : X → X)
  (sigma : Equiv.Perm.{apfNative_uD + 1} D) (flip : D → Bool)
  (r :
    @APFPaper5.K2.RearrangesFamily.{apfNative_uD, apfNative_uX, apfNative_uD} D X D reads (@id.{apfNative_uD + 1} D) h
      (@DFunLike.coe.{apfNative_uD + 1, apfNative_uD + 1, apfNative_uD + 1} (Equiv.Perm.{apfNative_uD + 1} D) D
        (fun (x : D) => D)
        (@EquivLike.toFunLike.{apfNative_uD + 1, apfNative_uD + 1, apfNative_uD + 1} (Equiv.Perm.{apfNative_uD + 1} D) D
          D (@Equiv.instEquivLike.{apfNative_uD + 1, apfNative_uD + 1} D D))
        sigma)
      flip)
  (hall : @APFB02.EveryCombinationHeld.{apfNative_uX, apfNative_uD} X D reads),
  @APFB02.StillHeldAfter.{apfNative_uX, apfNative_uD} X D reads h := by sorry
