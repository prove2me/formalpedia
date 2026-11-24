-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_changeLevel_eq_of_agree_coprime
-- name    : Formalism.ZeroFreeDirichlet.changeLevel_eq_of_agree_coprime
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:43:23.636822+00:00
-- url     : https://prove2.me/theorems/87da6f84-61e6-41b8-b0e7-415a849774a7
-- title:
--   Zero Free Dirichlet: change Level eq of agree coprime
-- statement:
--   The Zero Free Dirichlet construction uses the change Level eq of agree coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SameCharacterLFunctionOne.lean#L44-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SameCharacterLFunctionOne.lean#L44-L53

import Definitions.Def_Formalism_LandauZeroFreeBounds_SameCharacterLFunctionOne
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SameCharacterLFunctionOne
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

theorem Formalism.ZeroFreeDirichlet.changeLevel_eq_of_agree_coprime {q₁ q : ℕ} [NeZero q₁] [NeZero q] (χ₁ : DirichletCharacter ℂ q₁)
    (χ : DirichletCharacter ℂ q)
    (h : ∀ n : ℕ, Nat.Coprime n (q₁ * q) → χ₁ (n : ZMod q₁) = χ (n : ZMod q)) :
    DirichletCharacter.changeLevel (dvd_mul_right q₁ q) χ₁ =
      DirichletCharacter.changeLevel (dvd_mul_left q q₁) χ := by sorry
