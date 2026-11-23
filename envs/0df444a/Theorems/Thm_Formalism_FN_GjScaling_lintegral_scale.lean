-- Prove2me | Theorems.Thm_Formalism_FN_GjScaling_lintegral_scale
-- name    : Formalism.FN.GjScaling.lintegral_scale
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:00.751309+00:00
-- url     : https://prove2.me/theorems/75669edc-d608-47b9-9029-29f01ca707f4
-- title:
--   Gj Scaling: lintegral scale
-- statement:
--   The Gj Scaling construction uses the lintegral scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/GjScale.lean#L103-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/GjScale.lean#L103-L111

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

theorem Formalism.FN.GjScaling.lintegral_scale {κ : Type*} [Fintype κ] (h : (κ → ℝ) → ℝ≥0∞) {s : ℝ} (hs : 0 < s) :
    ∫⁻ y, h y = ENNReal.ofReal (s ^ Fintype.card κ) * ∫⁻ y, h (s • y) := by sorry
