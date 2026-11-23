-- Prove2me | Theorems.Thm_Formalism_FN_GjScaling_measurableSet_boxJ
-- name    : Formalism.FN.GjScaling.measurableSet_boxJ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:03.624028+00:00
-- url     : https://prove2.me/theorems/17f549bf-f11a-4e40-ab9c-7dd4876e1ae6
-- title:
--   Gj Scaling: measurable Set box J
-- statement:
--   The Gj Scaling construction uses the measurable Set box J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/GjScale.lean#L133-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/GjScale.lean#L133-L140

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
variable (n j : ℕ)

theorem Formalism.FN.GjScaling.measurableSet_boxJ : MeasurableSet (boxJ n j) := by sorry
