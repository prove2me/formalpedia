-- Prove2me | Theorems.Thm_Formalism_ZF_laH_diffOn
-- name    : Formalism.ZF.laH_diffOn
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:41:08.704951+00:00
-- url     : https://prove2.me/theorems/978c59c8-4b47-4f3b-bdd3-eedd69d96b89
-- title:
--   ZF: la H diff On
-- statement:
--   The ZF construction uses the la H diff On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/LaurentAtOne.lean#L19-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/LaurentAtOne.lean#L19-L30

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

theorem Formalism.ZF.laH_diffOn (y : ℝ) (hy : 0 < y) : DifferentiableOn ℂ (laHfun y) laU := by sorry
