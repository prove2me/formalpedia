-- Prove2me | Theorems.Thm_Formalism_FN_LowerVolumeBound_cross_mem
-- name    : Formalism.FN.LowerVolumeBound.cross_mem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:24:40.024062+00:00
-- url     : https://prove2.me/theorems/076ae28b-a198-57d5-bce5-cb77775850e2
-- title:
--   Lower Volume Bound: cross mem
-- statement:
--   The Lower Volume Bound construction uses the cross mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/MinkowskiIILowerOf.lean#L10-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/MinkowskiIILowerOf.lean#L10-L37

import Definitions.Def_Formalism_SuccessiveMinima_DefsMink
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_MinkowskiIILowerOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Metric Set ZSpan
open scoped Pointwise ENNReal
noncomputable section
open Formalism Formalism.FN Formalism.FN.LowerVolumeBound

theorem Formalism.FN.LowerVolumeBound.cross_mem {E : Type*} [AddCommGroup E] [Module ℝ E] {K : Set E} (hK : Convex ℝ K)
    (hs : ∀ x ∈ K, -x ∈ K) (h0 : (0 : E) ∈ K) {n : ℕ} (w : Fin n → E) (hw : ∀ i, w i ∈ K)
    (c : Fin n → ℝ) (hc : ∑ i, |c i| ≤ 1) : ∑ i, c i • w i ∈ K := by sorry
