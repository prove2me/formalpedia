-- Prove2me | Theorems.Thm_Formalism_ZF_laH_deriv_one
-- name    : Formalism.ZF.laH_deriv_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:41:08.584072+00:00
-- url     : https://prove2.me/theorems/7061c21b-6e33-4424-aad6-e39139292faa
-- title:
--   ZF: la H deriv one
-- statement:
--   The ZF construction uses the la H deriv one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/LaurentAtOne.lean#L34-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/LaurentAtOne.lean#L34-L48

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LaurentAtOne
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

theorem Formalism.ZF.laH_deriv_one (y : ℝ) (hy : 0 < y) :
    deriv (laHfun y) 1 = (y : ℂ) * Real.log y - (1 + Real.eulerMascheroniConstant) * y := by sorry
