-- Prove2me | Theorems.Thm_APFPaper5_K2_hold_words_compose
-- name    : APFPaper5.K2.hold_words_compose
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T20:31:15.079484+00:00
-- url     : https://prove2.me/theorems/c2de645a-27d6-4357-9f06-bf6e023a0940
-- title:
--   hold words compose
-- statement:
--   Result: hold words compose. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem hold_words_compose [Fintype ι]
--       (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop) {a : Context}
--       (W₁ W₂ : Word Frag a a) {D : Type uD} (reads : D → Raw a → Bool) (dist : ι → D)
--       (G : ι → ι → ℝ) (h₁ h₂ : Raw a → Raw a) (s₁ s₂ : ι → ι) (f₁ f₂ : ι → Bool)
--       (e₁ : ExecutesAs step W₁ h₁) (e₂ : ExecutesAs step W₂ h₂)
--       (r₁ : RearrangesFamily reads dist h₁ s₁ f₁) (r₂ : RearrangesFamily reads dist h₂ s₂ f₂) :
--       ExecutesAs step (W₁.append W₂) (h₂ ∘ h₁) ∧
--         RearrangesFamily reads dist (h₂ ∘ h₁) (s₁ ∘ s₂) (fun i => xor (f₂ i) (f₁ (s₂ i))) ∧
--         ∀ x y : ι → ℝ, holdScore G (s₁ ∘ s₂) x y = holdScore G s₂ (heldAfter s₁ x) y
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
--   ['Theorems.Thm_APFPaper5_K2_hold_words:139; pullbacks v39; source SHA-256 d254dc07751037f56a12a4a0422a606d6d4c387d9d62de81d3c3c2aba2633784']

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
universe apfNative_uI apfNative_uD apfNative_uC apfNative_uF apfNative_uW

theorem APFPaper5.K2.hold_words_compose :
∀ {ι : Type apfNative_uI} {Context : Type apfNative_uC} {Frag : Context → Context → Type apfNative_uF}
  {Raw : Context → Type apfNative_uW} [inst : Fintype.{apfNative_uI} ι]
  (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop) {a : Context}
  (W₁ W₂ : @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag a a) {D : Type apfNative_uD}
  (reads : D → Raw a → Bool) (dist : ι → D) (G : ι → ι → Real) (h₁ h₂ : Raw a → Raw a) (s₁ s₂ : ι → ι)
  (f₁ f₂ : ι → Bool)
  (e₁ : @APFPaper5.K2.ExecutesAs.{apfNative_uC, apfNative_uF, apfNative_uW} Context Frag Raw step a W₁ h₁)
  (e₂ : @APFPaper5.K2.ExecutesAs.{apfNative_uC, apfNative_uF, apfNative_uW} Context Frag Raw step a W₂ h₂)
  (r₁ : @APFPaper5.K2.RearrangesFamily.{apfNative_uI, apfNative_uW, apfNative_uD} ι (Raw a) D reads dist h₁ s₁ f₁)
  (r₂ : @APFPaper5.K2.RearrangesFamily.{apfNative_uI, apfNative_uW, apfNative_uD} ι (Raw a) D reads dist h₂ s₂ f₂),
  And
    (@APFPaper5.K2.ExecutesAs.{apfNative_uC, apfNative_uF, apfNative_uW} Context Frag Raw step a
      (@APFPaper1.Continuation.Word.append.{apfNative_uC, apfNative_uF} Context Frag a a a W₁ W₂)
      (@Function.comp.{apfNative_uW + 1, apfNative_uW + 1, apfNative_uW + 1} (Raw a) (Raw a) (Raw a) h₂ h₁))
    (And
      (@APFPaper5.K2.RearrangesFamily.{apfNative_uI, apfNative_uW, apfNative_uD} ι (Raw a) D reads dist
        (@Function.comp.{apfNative_uW + 1, apfNative_uW + 1, apfNative_uW + 1} (Raw a) (Raw a) (Raw a) h₂ h₁)
        (@Function.comp.{apfNative_uI + 1, apfNative_uI + 1, apfNative_uI + 1} ι ι ι s₁ s₂) fun (i : ι) =>
        Bool.xor (f₂ i) (f₁ (s₂ i)))
      (∀ (x y : ι → Real),
        @Eq.{1} Real
          (@APFPaper5.K2.holdScore.{apfNative_uI} ι inst G
            (@Function.comp.{apfNative_uI + 1, apfNative_uI + 1, apfNative_uI + 1} ι ι ι s₁ s₂) x y)
          (@APFPaper5.K2.holdScore.{apfNative_uI} ι inst G s₂ (@APFPaper5.K2.heldAfter.{apfNative_uI} ι s₁ x) y))) := by sorry
