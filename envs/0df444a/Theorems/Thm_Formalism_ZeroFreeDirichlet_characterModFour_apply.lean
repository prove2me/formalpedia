-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_characterModFour_apply
-- name    : Formalism.ZeroFreeDirichlet.characterModFour_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:43:19.934278+00:00
-- url     : https://prove2.me/theorems/8c9c7437-c54e-484e-bf6e-944c80ce3140
-- title:
--   Zero Free Dirichlet: character Mod Four apply
-- statement:
--   The Zero Free Dirichlet construction uses the character Mod Four apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/CharExists.lean#L38-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/CharExists.lean#L38-L39

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

theorem Formalism.ZeroFreeDirichlet.characterModFour_apply (a : ZMod 4) :
    characterModFour a = ((ZMod.χ₄ a : ℤ) : ℂ) := by sorry
