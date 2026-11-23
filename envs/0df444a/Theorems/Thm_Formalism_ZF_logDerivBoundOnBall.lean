-- Prove2me | Theorems.Thm_Formalism_ZF_logDerivBoundOnBall
-- name    : Formalism.ZF.logDerivBoundOnBall
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:36:10.309154+00:00
-- url     : https://prove2.me/theorems/f052d12a-88d6-4a81-93ea-72c369665494
-- title:
--   ZF: log Deriv Bound On Ball
-- statement:
--   The ZF construction uses the log Deriv Bound On Ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/LogDerivBound.lean#L42-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/LogDerivBound.lean#L42-L120

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LogDerivBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Metric
noncomputable section
open Formalism Formalism.ZF

theorem Formalism.ZF.logDerivBoundOnBall : LogDerivBound := by sorry
