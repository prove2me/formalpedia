-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_product_real_characters_sq_eq_one
-- name    : Formalism.ZeroFreeDirichlet.product_real_characters_sq_eq_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:44:11.101832+00:00
-- url     : https://prove2.me/theorems/67c7bbc1-763b-4d66-a461-954eca4a4039
-- title:
--   Zero Free Dirichlet: product real characters sq eq one
-- statement:
--   The Zero Free Dirichlet construction uses the product real characters sq eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelProductCharacterInequality.lean#L18-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelProductCharacterInequality.lean#L18-L31

import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelBoundSameCharacter
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAP
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelProductCharacterInequality
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

theorem Formalism.ZeroFreeDirichlet.product_real_characters_sq_eq_one {q₁ q : ℕ} [NeZero q₁] [NeZero q] (χ₁ : DirichletCharacter ℂ q₁) (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ (q₁ * q)) (h1 : χ₁ ^ 2 = 1) (h2 : χ ^ 2 = 1) (hψ : IsProdChar χ₁ χ ψ) :
    ψ ^ 2 = 1 := by sorry
