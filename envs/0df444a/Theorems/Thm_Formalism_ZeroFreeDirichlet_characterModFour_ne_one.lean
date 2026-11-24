-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_characterModFour_ne_one
-- name    : Formalism.ZeroFreeDirichlet.characterModFour_ne_one
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:43:40.623097+00:00
-- url     : https://prove2.me/theorems/d9b5fa1a-2697-40d3-9297-2c431cf72623
-- title:
--   Zero Free Dirichlet: character Mod Four ne one
-- statement:
--   The Zero Free Dirichlet construction uses the character Mod Four ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/CharExists.lean#L46-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/CharExists.lean#L46-L53

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

theorem Formalism.ZeroFreeDirichlet.characterModFour_ne_one : characterModFour ≠ 1 := by sorry
