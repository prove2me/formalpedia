-- Prove2me | Theorems.Thm_APFPaper5_K2_holdScoreNull_before
-- name    : APFPaper5.K2.holdScoreNull_before
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T20:40:24.688061+00:00
-- url     : https://prove2.me/theorems/a9ba13b9-2ed7-4020-99f8-33d1e0d0462b
-- title:
--   holdScoreNull before
-- statement:
--   Result: holdScoreNull before. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem holdScoreNull_before {κ : Type uK} [Fintype κ] (G : ι → ι → ℝ) (coef : κ → ℝ)
--       (s : κ → ι → ι) (r : ι → ι) (h : HoldScoreNull G coef s) :
--       HoldScoreNull G coef (fun k => r ∘ s k)
--   ```
--
--   Module context and limits: KeepsTable remains explicit, as do symmetry, faithful diagonal and SourceCounted where used. The author-adopted reading is not a derivation from installed inputs. Inverse permutations and null-combination closure do not establish admitted inverse words or full K2 closure.
--
--   Source scope parameters:
--
--   ```lean
--   universe uI uK
--   variable {ι : Type uI}
--   variable [Fintype ι]
--   variable {D P R Record : Type*} {ι' : Type*} [Fintype ι'] [DecidableEq ι'] [DecidableEq D]
--     [Fintype Record]
--   ```
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper5_K2_holds_keep_table:82; pullbacks v39; source SHA-256 504b1bcaf41d4218cb5bab47f8fe935a16187393f6044caef3b236d53fed36dd']

import Definitions.Def_APFPaper5_K2_holds_keep_table_Vocabulary
import Definitions.Def_APFPaper5_K2_HoldScore
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
set_option autoImplicit false
universe apfNative_uI apfNative_uK

theorem APFPaper5.K2.holdScoreNull_before :
∀ {ι : Type apfNative_uI} [inst : Fintype.{apfNative_uI} ι] {κ : Type apfNative_uK} [inst_1 : Fintype.{apfNative_uK} κ]
  (G : ι → ι → Real) (coef : κ → Real) (s : κ → ι → ι) (r : ι → ι)
  (h : @APFPaper5.K2.HoldScoreNull.{apfNative_uI, apfNative_uK} ι inst κ inst_1 G coef s),
  @APFPaper5.K2.HoldScoreNull.{apfNative_uI, apfNative_uK} ι inst κ inst_1 G coef fun (k : κ) =>
    @Function.comp.{apfNative_uI + 1, apfNative_uI + 1, apfNative_uI + 1} ι ι ι r (s k) := by sorry
