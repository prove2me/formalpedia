-- Prove2me | Theorems.Thm_Formalism_FN_GjScaling_tm_empty
-- name    : Formalism.FN.GjScaling.tm_empty
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:06.394911+00:00
-- url     : https://prove2.me/theorems/4c41d00b-f55b-49b0-ac1e-a03cd86e4d84
-- title:
--   Gj Scaling: tm empty
-- statement:
--   The Gj Scaling construction uses the tm empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/GjScale.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/GjScale.lean#L23-L24

import Definitions.Def_Formalism_SuccessiveMinima_DefsMink
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_GjScale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Metric Set
open scoped Pointwise ENNReal
noncomputable section
open Formalism Formalism.FN
open Formalism.FN.GjScaling
variable {ι : Type*} [Fintype ι]

theorem Formalism.FN.GjScaling.tm_empty : tm (∅ : Set (ι → ℝ)) = 0 := by sorry
