-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_zFRDirichlet
-- name    : Formalism.ZeroFreeDirichlet.zFRDirichlet
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:42:35.552061+00:00
-- url     : https://prove2.me/theorems/50f541b6-5df0-406f-b6dd-78982cfac6a1
-- title:
--   Zero Free Dirichlet: z FRDirichlet
-- statement:
--   The Zero Free Dirichlet construction uses the z FRDirichlet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/NoZeroComplex.lean#L32-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/NoZeroComplex.lean#L32-L33

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

theorem Formalism.ZeroFreeDirichlet.zFRDirichlet : ZFRDirichlet := by sorry
