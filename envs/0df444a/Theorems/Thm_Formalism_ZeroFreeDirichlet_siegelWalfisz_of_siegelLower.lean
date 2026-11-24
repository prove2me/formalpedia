-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_siegelWalfisz_of_siegelLower
-- name    : Formalism.ZeroFreeDirichlet.siegelWalfisz_of_siegelLower
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:47:49.323815+00:00
-- url     : https://prove2.me/theorems/55c26376-dba1-4b43-bdc5-69bb0772f589
-- title:
--   Zero Free Dirichlet: siegel Walfisz of siegel Lower
-- statement:
--   The Zero Free Dirichlet construction uses the siegel Walfisz of siegel Lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/SiegelWalfiszAPOfSiegelLower.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/SiegelWalfiszAPOfSiegelLower.lean#L29-L30

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplex
import Definitions.Def_Formalism_LandauZeroFreeBounds_FinalSiegel
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LandauLocal3
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronChi
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_RectShiftChi
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SmoothChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PsiChiBoundOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LDerivNearOne
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ExcBoundOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelWalfiszOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelWalfiszAPOf
import Definitions.Def_Formalism_ZeroFreeRegion_LogDerivRegion
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.siegelWalfisz_of_siegelLower (hS : SiegelLower) : SiegelWalfisz := by sorry
