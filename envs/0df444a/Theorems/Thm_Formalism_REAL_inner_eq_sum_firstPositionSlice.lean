-- Prove2me | Theorems.Thm_Formalism_REAL_inner_eq_sum_firstPositionSlice
-- name    : Formalism.REAL.inner_eq_sum_firstPositionSlice
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:14.623858+00:00
-- url     : https://prove2.me/theorems/841db835-1dfc-43ae-9098-a49cdc2dd839
-- title:
--   REAL: inner eq sum first Position Slice
-- statement:
--   The REAL construction uses the inner eq sum first Position Slice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L479-L482
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L479-L482

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

theorem Formalism.REAL.inner_eq_sum_firstPositionSlice (F G : Arr V n (j+1)) :
    ⟪F, G⟫_ℂ = ∑ α' : Fin j → Fin n × Fin n, ⟪sliceLin V n α' F, sliceLin V n α' G⟫_ℂ := by sorry
