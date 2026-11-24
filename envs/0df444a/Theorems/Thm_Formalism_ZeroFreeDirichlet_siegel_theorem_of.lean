-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_siegel_theorem_of
-- name    : Formalism.ZeroFreeDirichlet.siegel_theorem_of
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:44:32.597576+00:00
-- url     : https://prove2.me/theorems/ed7013e9-68e9-4a7a-a90c-952654f403e8
-- title:
--   Zero Free Dirichlet: siegel theorem of
-- statement:
--   The Zero Free Dirichlet construction uses the siegel theorem of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelOf.lean#L9-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelOf.lean#L9-L64

import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelProductCharacterInequality
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelOf
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

theorem Formalism.ZeroFreeDirichlet.siegel_theorem_of : SiegelOf := by sorry
