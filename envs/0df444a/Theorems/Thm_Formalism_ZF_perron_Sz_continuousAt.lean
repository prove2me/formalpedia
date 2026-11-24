-- Prove2me | Theorems.Thm_Formalism_ZF_perron_Sz_continuousAt
-- name    : Formalism.ZF.perron_Sz_continuousAt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:41:29.24519+00:00
-- url     : https://prove2.me/theorems/7d628e37-c3ad-4e4f-a2eb-89ab408adc93
-- title:
--   ZF: perron Sz continuous At
-- statement:
--   The ZF construction uses the perron Sz continuous At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/Perron.lean#L48-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/Perron.lean#L48-L105

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology ArithmeticFunction
open scoped LSeries.notation
noncomputable section
open Formalism Formalism.ZF

theorem Formalism.ZF.perron_Sz_continuousAt (y : ℝ) : ContinuousAt (fun x => (Formalism.Sz x : ℂ)) y := by sorry
