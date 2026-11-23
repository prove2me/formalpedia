-- Prove2me | Theorems.Thm_Formalism_FN_GjScaling_tm_add_singleton
-- name    : Formalism.FN.GjScaling.tm_add_singleton
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:13.477218+00:00
-- url     : https://prove2.me/theorems/ce4d3956-d963-48ae-8617-4b5699d706cf
-- title:
--   Gj Scaling: tm add singleton
-- statement:
--   The Gj Scaling construction uses the tm add singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/GjScale.lean#L65-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/GjScale.lean#L65-L101

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

theorem Formalism.FN.GjScaling.tm_add_singleton {B : Set (ι → ℝ)} (hB : IsOpen B) (c : ι → ℝ) :
    tm (B + {c}) = tm B := by sorry
