-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_realSmallT
-- name    : Formalism.ZeroFreeDirichlet.realSmallT
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:46:04.316163+00:00
-- url     : https://prove2.me/theorems/f618339f-d3ea-4953-9208-2b062e8ef3d0
-- title:
--   Zero Free Dirichlet: real Small T
-- statement:
--   The Zero Free Dirichlet construction uses the real Small T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/NoZeroComplex.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/NoZeroComplex.lean#L26-L27

import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LocalZeroExpansionWithMultiplicity
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LRight
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_Positivity
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_TrivLogDeriv
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_TrivReal
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LocalZerosOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_RealLargeTOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_RealSmallTOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_TwoRealOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ZFRDirichletOf
import Definitions.Def_Formalism_ZeroFreeRegion_FinalZFR
import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.realSmallT : RealSmallT := by sorry
