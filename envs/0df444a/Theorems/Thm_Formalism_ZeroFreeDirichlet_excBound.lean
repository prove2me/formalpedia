-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_excBound
-- name    : Formalism.ZeroFreeDirichlet.excBound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:53:08.956977+00:00
-- url     : https://prove2.me/theorems/1705145d-78f1-40b0-93c4-cfcc8c0247ba
-- title:
--   Zero Free Dirichlet: exc Bound
-- statement:
--   The Zero Free Dirichlet construction uses the exc Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/SiegelWalfiszAPOfSiegelLower.lean#L32-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/SiegelWalfiszAPOfSiegelLower.lean#L32-L32

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

theorem Formalism.ZeroFreeDirichlet.excBound : ExcBound := by sorry
