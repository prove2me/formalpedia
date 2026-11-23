-- Prove2me | Theorems.Thm_Formalism_REAL_pointwiseAction_mul_permutePositions
-- name    : Formalism.REAL.pointwiseAction_mul_permutePositions
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:38.588092+00:00
-- url     : https://prove2.me/theorems/1e199e5b-13c7-4bd7-8f26-65d1191c8caa
-- title:
--   REAL: pointwise Action mul permute Positions
-- statement:
--   The REAL construction uses the pointwise Action mul permute Positions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L273-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L273-L276

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

theorem Formalism.REAL.pointwiseAction_mul_permutePositions (E : Fin n → Fin n → Module.End ℂ V) (σ : Equiv.Perm (Fin j)) (c d : Fin n) :
    ptE E c d * permArr V n σ = permArr V n σ * ptE E c d := by sorry
