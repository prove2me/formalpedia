-- Prove2me | Theorems.Thm_Formalism_FN_GjScaling_Zv_neg
-- name    : Formalism.FN.GjScaling.Zv_neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:55.546853+00:00
-- url     : https://prove2.me/theorems/685acd50-dca8-4976-a472-555132b8e82e
-- title:
--   Gj Scaling: Zv neg
-- statement:
--   The Gj Scaling construction uses the Zv neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/GjScale.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/GjScale.lean#L31-L33

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

theorem Formalism.FN.GjScaling.Zv_neg {a : ι → ℝ} (ha : a ∈ Zv ι) : -a ∈ Zv ι := by sorry
