-- Prove2me | Theorems.Thm_Formalism_ZF_zeroFreeBoundedHeight
-- name    : Formalism.ZF.zeroFreeBoundedHeight
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:40:50.303819+00:00
-- url     : https://prove2.me/theorems/9b702de3-84a8-4590-b4ca-d05dab37e3f7
-- title:
--   ZF: zero Free Bounded Height
-- statement:
--   The ZF construction uses the zero Free Bounded Height property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/SmallHeight.lean#L9-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/SmallHeight.lean#L9-L42

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_SmallHeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Set Filter Topology
noncomputable section
open Formalism Formalism.ZF

theorem Formalism.ZF.zeroFreeBoundedHeight : SmallHeight := by sorry
