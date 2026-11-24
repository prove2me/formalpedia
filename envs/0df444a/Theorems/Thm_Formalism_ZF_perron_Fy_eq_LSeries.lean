-- Prove2me | Theorems.Thm_Formalism_ZF_perron_Fy_eq_LSeries
-- name    : Formalism.ZF.perron_Fy_eq_LSeries
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:41:34.288172+00:00
-- url     : https://prove2.me/theorems/81d4373b-e61a-4d97-91fd-d6e735ebf497
-- title:
--   ZF: perron Fy eq LSeries
-- statement:
--   The ZF construction uses the perron Fy eq LSeries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/Perron.lean#L145-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/Perron.lean#L145-L149

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

theorem Formalism.ZF.perron_Fy_eq_LSeries (y : ℝ) (w : ℂ) (hw : 1 < w.re) :
    Fy y w = LSeries ↗Λ w * (y : ℂ) ^ w / (w * (w - 1)) := by sorry
