-- Prove2me | Theorems.Thm_Formalism_ZF_logDerivBoundInRegionOfBounds
-- name    : Formalism.ZF.logDerivBoundInRegionOfBounds
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:42:29.697116+00:00
-- url     : https://prove2.me/theorems/dff09fdc-e260-4cfa-bb72-bf62feee4b59
-- title:
--   ZF: log Deriv Bound In Region Of Bounds
-- statement:
--   The ZF construction uses the log Deriv Bound In Region Of Bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/LogDerivRegionOf.lean#L10-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/LogDerivRegionOf.lean#L10-L85

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LdrMid
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LogDerivRegionOf
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
open Formalism Formalism.ZF

theorem Formalism.ZF.logDerivBoundInRegionOfBounds : LogDerivRegionOf := by sorry
