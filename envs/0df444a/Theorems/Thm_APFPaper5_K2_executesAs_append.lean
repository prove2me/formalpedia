-- Prove2me | Theorems.Thm_APFPaper5_K2_executesAs_append
-- name    : APFPaper5.K2.executesAs_append
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T20:31:04.657202+00:00
-- url     : https://prove2.me/theorems/b1f1f091-9af6-4891-8661-0b002ae0c5fb
-- title:
--   executesAs append
-- statement:
--   Result: executesAs append. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem executesAs_append (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop) {a : Context}
--       (W₁ W₂ : Word Frag a a) (h₁ h₂ : Raw a → Raw a)
--       (e₁ : ExecutesAs step W₁ h₁) (e₂ : ExecutesAs step W₂ h₂) :
--       ExecutesAs step (W₁.append W₂) (h₂ ∘ h₁)
--   ```
--
--   Module context and limits: ExecutesAs assumes total deterministic execution as the supplied map. Rearrangement uniqueness additionally requires EveryCombinationHeld and an injective listing. The score result does not establish bills, admission, inverse-word availability or that every word is a hold.
--
--   Source scope parameters:
--
--   ```lean
--   universe uI uX uD uC uF uW
--   variable {ι : Type uI}
--   variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uW}
--   ```
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper5_K2_hold_words:56; pullbacks v39; source SHA-256 d254dc07751037f56a12a4a0422a606d6d4c387d9d62de81d3c3c2aba2633784']

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
import Mathlib.Data.Finset.Insert
set_option autoImplicit false
universe apfNative_uC apfNative_uF apfNative_uW

theorem APFPaper5.K2.executesAs_append :
∀ {Context : Type apfNative_uC} {Frag : Context → Context → Type apfNative_uF} {Raw : Context → Type apfNative_uW}
  (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop) {a : Context}
  (W₁ W₂ : @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag a a) (h₁ h₂ : Raw a → Raw a)
  (e₁ : @APFPaper5.K2.ExecutesAs.{apfNative_uC, apfNative_uF, apfNative_uW} Context Frag Raw step a W₁ h₁)
  (e₂ : @APFPaper5.K2.ExecutesAs.{apfNative_uC, apfNative_uF, apfNative_uW} Context Frag Raw step a W₂ h₂),
  @APFPaper5.K2.ExecutesAs.{apfNative_uC, apfNative_uF, apfNative_uW} Context Frag Raw step a
    (@APFPaper1.Continuation.Word.append.{apfNative_uC, apfNative_uF} Context Frag a a a W₁ W₂)
    (@Function.comp.{apfNative_uW + 1, apfNative_uW + 1, apfNative_uW + 1} (Raw a) (Raw a) (Raw a) h₂ h₁) := by sorry
