-- Prove2me | Theorems.Thm_Formalism_ZF_perron_continuous_mxS
-- name    : Formalism.ZF.perron_continuous_mxS
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:40:37.196836+00:00
-- url     : https://prove2.me/theorems/4d099c64-c5e1-49bf-a856-def8b91eb7ee
-- title:
--   ZF: perron continuous mx S
-- statement:
--   The ZF construction uses the perron continuous mx S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/Perron.lean#L44-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/Perron.lean#L44-L46

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

theorem Formalism.ZF.perron_continuous_mxS (n : ℕ) : Continuous (Formalism.mxS n) := by sorry
