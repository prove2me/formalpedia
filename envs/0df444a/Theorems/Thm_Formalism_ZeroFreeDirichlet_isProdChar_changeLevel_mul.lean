-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_isProdChar_changeLevel_mul
-- name    : Formalism.ZeroFreeDirichlet.isProdChar_changeLevel_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:42:46.823058+00:00
-- url     : https://prove2.me/theorems/6f5e5593-864c-45ab-a1b0-47dda6307757
-- title:
--   Zero Free Dirichlet: is Prod Char change Level mul
-- statement:
--   The Zero Free Dirichlet construction uses the is Prod Char change Level mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/CharExists.lean#L7-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/CharExists.lean#L7-L31

import Definitions.Def_Formalism_LandauZeroFreeBounds_SameCharacterLFunctionOne
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_CharExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.isProdChar_changeLevel_mul {q₁ q₂ : ℕ} (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂) :
    IsProdChar χ₁ χ₂ (DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁ *
      DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂) := by sorry
