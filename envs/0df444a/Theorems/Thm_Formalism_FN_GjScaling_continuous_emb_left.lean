-- Prove2me | Theorems.Thm_Formalism_FN_GjScaling_continuous_emb_left
-- name    : Formalism.FN.GjScaling.continuous_emb_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:01.041466+00:00
-- url     : https://prove2.me/theorems/fecead8b-b9d0-4b4d-99b4-87ec79ee57c1
-- title:
--   Gj Scaling: continuous emb left
-- statement:
--   The Gj Scaling construction uses the continuous emb left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/GjScale.lean#L124-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/GjScale.lean#L124-L131

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

theorem Formalism.FN.GjScaling.continuous_emb_left (y : {i : Fin n // ¬ (i : ℕ) < j} → ℝ) :
    Continuous fun u => emb n j u y := by sorry
