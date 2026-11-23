-- Prove2me | Theorems.Thm_Formalism_FN_GjScaling_card_compl
-- name    : Formalism.FN.GjScaling.card_compl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:17:56.085316+00:00
-- url     : https://prove2.me/theorems/8b11f524-101b-4238-9bcc-52a3bb251e8d
-- title:
--   Gj Scaling: card compl
-- statement:
--   The Gj Scaling construction uses the card compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/GjScale.lean#L230-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/GjScale.lean#L230-L242

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

theorem Formalism.FN.GjScaling.card_compl (hj : j ≤ n) : Fintype.card {i : Fin n // ¬ (i : ℕ) < j} = n - j := by sorry
