-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_card_le_of_chars
-- name    : Formalism.L2.FormalSeriesBounds.UpFBr.Pl.card_le_of_chars
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:30:17.704801+00:00
-- url     : https://prove2.me/theorems/751b2a03-8b32-4b57-981c-d22b82083ef0
-- title:
--   Pl: card le of chars
-- statement:
--   The Pl construction uses the card le of chars property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/DetNeZeroOfChars.lean#L50-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/DetNeZeroOfChars.lean#L50-L62

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieUpFBrPl
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_DetNeZeroOfChars
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.UpFBr Formalism.L2.FormalSeriesBounds.UpFBr.Pl
variable {F A L : Type} [CommRing F] [CommRing A] [Algebra F A] [Field L] {ι' ι : Type} [Fintype ι'] [Fintype ι]

theorem Formalism.L2.FormalSeriesBounds.UpFBr.Pl.card_le_of_chars (χ : ι' → A →+* L) (hχ : Function.Injective χ) (φ : F →+* L)
    (hφ : ∀ j r, χ j (algebraMap F A r) = φ r) (e : A) (he : ∀ j, χ j e = 1) (b : ι → A)
    (hb : ∀ x : A, ∃ r : ι → F, e * x = ∑ i, r i • b i) : Fintype.card ι' ≤ Fintype.card ι := by sorry
