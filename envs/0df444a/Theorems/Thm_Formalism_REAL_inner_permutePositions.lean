-- Prove2me | Theorems.Thm_Formalism_REAL_inner_permutePositions
-- name    : Formalism.REAL.inner_permutePositions
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:43.36326+00:00
-- url     : https://prove2.me/theorems/45eba6d9-93a4-46e0-afce-761c517b0124
-- title:
--   REAL: inner permute Positions
-- statement:
--   The REAL construction uses the inner permute Positions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L473-L477
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L473-L477

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

theorem Formalism.REAL.inner_permutePositions (σ : Equiv.Perm (Fin j)) (F G : Arr V n j) :
    ⟪permArr V n σ F, permArr V n σ G⟫_ℂ = ⟪F, G⟫_ℂ := by sorry
