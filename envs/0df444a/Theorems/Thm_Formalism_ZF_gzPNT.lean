-- Prove2me | Theorems.Thm_Formalism_ZF_gzPNT
-- name    : Formalism.ZF.gzPNT
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:36:20.929803+00:00
-- url     : https://prove2.me/theorems/72c2d1fd-958e-4f72-b176-ea4c43f072f5
-- title:
--   ZF: gz PNT
-- statement:
--   The ZF construction uses the gz PNT property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/LogDerivRegion.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/LogDerivRegion.lean#L20-L21

import Definitions.Def_Formalism_ZeroFreeRegion_FinalZFR
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LogDerivRegionOf
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_RectDoublePole
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LaurentAtOne
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_RectShiftOf
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_GzPNTOf
import Definitions.Def_Formalism_ZeroFreeRegion_LogDerivRegion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ZF

theorem Formalism.ZF.gzPNT : GzPNT := by sorry
