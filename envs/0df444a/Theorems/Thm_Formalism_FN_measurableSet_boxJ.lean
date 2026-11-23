-- Prove2me | Theorems.Thm_Formalism_FN_measurableSet_boxJ
-- name    : Formalism.FN.measurableSet_boxJ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:59.196588+00:00
-- url     : https://prove2.me/theorems/ed3f0e39-c931-4c00-81a3-2955699a6334
-- title:
--   FN: measurable Set box J
-- statement:
--   The FN construction uses the measurable Set box J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/GjLevel.lean#L10-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/GjLevel.lean#L10-L17

import Definitions.Def_Formalism_SuccessiveMinima_DefsMink
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_GjLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped Pointwise ENNReal
noncomputable section
open Formalism Formalism.FN

theorem Formalism.FN.measurableSet_boxJ (n j : ℕ) : MeasurableSet (boxJ n j) := by sorry
