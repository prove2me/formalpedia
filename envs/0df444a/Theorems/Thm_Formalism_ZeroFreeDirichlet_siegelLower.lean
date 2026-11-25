-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_siegelLower
-- name    : Formalism.ZeroFreeDirichlet.siegelLower
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:38:37.494671+00:00
-- url     : https://prove2.me/theorems/b03487a5-b8f9-48a1-b826-4724e693a8df
-- title:
--   Zero Free Dirichlet: siegel Lower
-- statement:
--   The Zero Free Dirichlet construction uses the siegel Lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/FinalSiegel.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/FinalSiegel.lean#L17-L19

import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_CharExists
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_BqCoeff
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_BqEntire
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_BqGrowth
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LFunctionOneUpperBound
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_BqKeyOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ZetaNegReal
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LRealPos
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SameCharacterLFunctionOne
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_FinalSiegel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.siegelLower : SiegelLower := by sorry
