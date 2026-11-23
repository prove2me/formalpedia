-- Prove2me | Theorems.Thm_Formalism_FN_GjScaling_tm_mono
-- name    : Formalism.FN.GjScaling.tm_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:09.168509+00:00
-- url     : https://prove2.me/theorems/7c5c17c3-5b5d-4182-b39f-1464b10fc723
-- title:
--   Gj Scaling: tm mono
-- statement:
--   The Gj Scaling construction uses the tm mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/GjScale.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/GjScale.lean#L19-L21

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

theorem Formalism.FN.GjScaling.tm_mono {B B' : Set (ι → ℝ)} (h : B ⊆ B') : tm B ≤ tm B' := by sorry
