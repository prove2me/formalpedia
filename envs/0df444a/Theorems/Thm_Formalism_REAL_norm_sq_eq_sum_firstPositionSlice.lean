-- Prove2me | Theorems.Thm_Formalism_REAL_norm_sq_eq_sum_firstPositionSlice
-- name    : Formalism.REAL.norm_sq_eq_sum_firstPositionSlice
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:25:14.785739+00:00
-- url     : https://prove2.me/theorems/b494d326-4592-49b7-8686-5323e0774450
-- title:
--   REAL: norm sq eq sum first Position Slice
-- statement:
--   The REAL construction uses the norm sq eq sum first Position Slice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L510-L513
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L510-L513

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n j : ℕ}

theorem Formalism.REAL.norm_sq_eq_sum_firstPositionSlice (F : Arr V n (j+1)) :
    ‖F‖ ^ 2 = ∑ α' : Fin j → Fin n × Fin n, ‖sliceLin V n α' F‖ ^ 2 := by sorry
