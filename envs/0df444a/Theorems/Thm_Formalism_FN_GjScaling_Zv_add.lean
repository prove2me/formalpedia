-- Prove2me | Theorems.Thm_Formalism_FN_GjScaling_Zv_add
-- name    : Formalism.FN.GjScaling.Zv_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:00.06103+00:00
-- url     : https://prove2.me/theorems/a6169fd5-00f4-476f-bd10-f7e44ebab51c
-- title:
--   Gj Scaling: Zv add
-- statement:
--   The Gj Scaling construction uses the Zv add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/GjScale.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/GjScale.lean#L26-L29

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

theorem Formalism.FN.GjScaling.Zv_add {a b : ι → ℝ} (ha : a ∈ Zv ι) (hb : b ∈ Zv ι) : a + b ∈ Zv ι := by sorry
