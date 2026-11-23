-- Prove2me | Theorems.Thm_Formalism_REAL_firstPositionSlice_pointwiseAction
-- name    : Formalism.REAL.firstPositionSlice_pointwiseAction
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:15.556271+00:00
-- url     : https://prove2.me/theorems/2ea34b0f-84f2-4268-a1ea-b7d76e307d03
-- title:
--   REAL: first Position Slice pointwise Action
-- statement:
--   The REAL construction uses the first Position Slice pointwise Action property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L308-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L308-L311

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
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ}

theorem Formalism.REAL.firstPositionSlice_pointwiseAction (E : Fin n → Fin n → Module.End ℂ V) (α' : Fin j → Fin n × Fin n) (c d : Fin n)
    (F : Arr V n (j+1)) : sliceLin V n α' (ptE E c d F) = ptE E c d (sliceLin V n α' F) := by sorry
