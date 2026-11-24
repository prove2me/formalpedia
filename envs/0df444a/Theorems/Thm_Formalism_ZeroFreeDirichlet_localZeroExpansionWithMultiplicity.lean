-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_localZeroExpansionWithMultiplicity
-- name    : Formalism.ZeroFreeDirichlet.localZeroExpansionWithMultiplicity
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:42:30.524023+00:00
-- url     : https://prove2.me/theorems/f7e76eca-3f38-4034-b807-926f19e12754
-- title:
--   Zero Free Dirichlet: local Zero Expansion With Multiplicity
-- statement:
--   The Zero Free Dirichlet construction uses the local Zero Expansion With Multiplicity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LocalZeroExpansionWithMultiplicity.lean#L8-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LocalZeroExpansionWithMultiplicity.lean#L8-L11

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ExistsLocalZeroExpansionOfBound
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LocalZeroExpansionWithMultiplicity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.localZeroExpansionWithMultiplicity : LandauLocal2 := by sorry
