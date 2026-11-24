-- Prove2me | Theorems.Thm_Formalism_REAL_inner_positionAction
-- name    : Formalism.REAL.inner_positionAction
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:23:25.146431+00:00
-- url     : https://prove2.me/theorems/1236b56e-0115-42a6-b8c8-a521bba8af0b
-- title:
--   REAL: inner position Action
-- statement:
--   The REAL construction uses the inner position Action property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L82-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L82-L120

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

theorem Formalism.REAL.inner_positionAction (i : Fin j) (c d : Fin n) (F G : Arr V n j) :
    ⟪factorAction i c d F, G⟫_ℂ = ⟪F, factorAction i d c G⟫_ℂ := by sorry
