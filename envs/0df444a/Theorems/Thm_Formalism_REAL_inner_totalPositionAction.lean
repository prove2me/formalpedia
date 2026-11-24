-- Prove2me | Theorems.Thm_Formalism_REAL_inner_totalPositionAction
-- name    : Formalism.REAL.inner_totalPositionAction
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:23:19.3701+00:00
-- url     : https://prove2.me/theorems/193ecb8e-9a20-4eb5-aa84-755c3db143e5
-- title:
--   REAL: inner total Position Action
-- statement:
--   The REAL construction uses the inner total Position Action property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L122-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L122-L124

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

theorem Formalism.REAL.inner_totalPositionAction (c d : Fin n) (F G : Arr V n j) :
    ⟪positionsE V n j c d F, G⟫_ℂ = ⟪F, positionsE V n j d c G⟫_ℂ := by sorry
