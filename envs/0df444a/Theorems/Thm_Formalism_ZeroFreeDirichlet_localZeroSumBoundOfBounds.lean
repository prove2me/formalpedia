-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_localZeroSumBoundOfBounds
-- name    : Formalism.ZeroFreeDirichlet.localZeroSumBoundOfBounds
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:42:27.900364+00:00
-- url     : https://prove2.me/theorems/7cae94ff-5e6c-4cce-bce7-24ea24f841ac
-- title:
--   Zero Free Dirichlet: local Zero Sum Bound Of Bounds
-- statement:
--   The Zero Free Dirichlet construction uses the local Zero Sum Bound Of Bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LocalZerosOf.lean#L44-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LocalZerosOf.lean#L44-L137

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LocalZerosOf
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

theorem Formalism.ZeroFreeDirichlet.localZeroSumBoundOfBounds : LocalZerosOf := by sorry
