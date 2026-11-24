-- Prove2me | Theorems.Thm_Formalism_ZF_zetaPrimeSumErrorBoundOfBounds
-- name    : Formalism.ZF.zetaPrimeSumErrorBoundOfBounds
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:40:50.235604+00:00
-- url     : https://prove2.me/theorems/25107faf-6579-44e7-974f-b54341423dcb
-- title:
--   ZF: zeta Prime Sum Error Bound Of Bounds
-- statement:
--   The ZF construction uses the zeta Prime Sum Error Bound Of Bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/GzPNTOf.lean#L48-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/GzPNTOf.lean#L48-L93

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_AbsZetaPrimeSumErrorLeOfOneLe
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_AbsZetaPrimeSumErrorLeOfLarge
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_GzPNTOf
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

theorem Formalism.ZF.zetaPrimeSumErrorBoundOfBounds : GzPNTOf := by sorry
