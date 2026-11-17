-- Prove2me | Theorems.Thm_APFPaper5_K2_rearrangement_unique
-- name    : APFPaper5.K2.rearrangement_unique
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T20:31:09.655104+00:00
-- url     : https://prove2.me/theorems/b134fa51-2347-4ae8-80d4-a71629d8f785
-- title:
--   rearrangement unique
-- statement:
--   Result: rearrangement unique. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem rearrangement_unique {X : Type uX} {D : Type uD} (reads : D → X → Bool)
--       (hall : APFB02.EveryCombinationHeld reads) (dist : ι → D) (hinj : Function.Injective dist)
--       (h : X → X) (s s' : ι → ι) (f f' : ι → Bool)
--       (r : RearrangesFamily reads dist h s f) (r' : RearrangesFamily reads dist h s' f') :
--       s = s' ∧ f = f'
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
--   ['Theorems.Thm_APFPaper5_K2_hold_words:77; pullbacks v39; source SHA-256 d254dc07751037f56a12a4a0422a606d6d4c387d9d62de81d3c3c2aba2633784']

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
universe apfNative_uI apfNative_uX apfNative_uD

theorem APFPaper5.K2.rearrangement_unique :
∀ {ι : Type apfNative_uI} {X : Type apfNative_uX} {D : Type apfNative_uD} (reads : D → X → Bool)
  (hall : @APFB02.EveryCombinationHeld.{apfNative_uX, apfNative_uD} X D reads) (dist : ι → D)
  (hinj : @Function.Injective.{apfNative_uI + 1, apfNative_uD + 1} ι D dist) (h : X → X) (s s' : ι → ι)
  (f f' : ι → Bool)
  (r : @APFPaper5.K2.RearrangesFamily.{apfNative_uI, apfNative_uX, apfNative_uD} ι X D reads dist h s f)
  (r' : @APFPaper5.K2.RearrangesFamily.{apfNative_uI, apfNative_uX, apfNative_uD} ι X D reads dist h s' f'),
  And (@Eq.{apfNative_uI + 1} (ι → ι) s s') (@Eq.{apfNative_uI + 1} (ι → Bool) f f') := by sorry
