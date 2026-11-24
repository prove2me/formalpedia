-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_characterModFour_sq
-- name    : Formalism.ZeroFreeDirichlet.characterModFour_sq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:43:53.222038+00:00
-- url     : https://prove2.me/theorems/9b428adc-a9e4-4296-9c2b-4381d4b4b042
-- title:
--   Zero Free Dirichlet: character Mod Four sq
-- statement:
--   The Zero Free Dirichlet construction uses the character Mod Four sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/CharExists.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/CharExists.lean#L41-L44

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

theorem Formalism.ZeroFreeDirichlet.characterModFour_sq : characterModFour ^ 2 = 1 := by sorry
