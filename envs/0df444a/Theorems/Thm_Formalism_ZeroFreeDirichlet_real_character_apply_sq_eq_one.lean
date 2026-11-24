-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_real_character_apply_sq_eq_one
-- name    : Formalism.ZeroFreeDirichlet.real_character_apply_sq_eq_one
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:43:50.0039+00:00
-- url     : https://prove2.me/theorems/24de1466-6b0c-44c7-a098-8293447d3f9f
-- title:
--   Zero Free Dirichlet: real character apply sq eq one
-- statement:
--   The Zero Free Dirichlet construction uses the real character apply sq eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelProductCharacterInequality.lean#L10-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelProductCharacterInequality.lean#L10-L16

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

theorem Formalism.ZeroFreeDirichlet.real_character_apply_sq_eq_one {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {n : ℕ}
    (hn : n.Coprime q) : χ (n : ZMod q) * χ (n : ZMod q) = 1 := by sorry
