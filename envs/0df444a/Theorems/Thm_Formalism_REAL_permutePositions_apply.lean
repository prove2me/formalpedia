-- Prove2me | Theorems.Thm_Formalism_REAL_permutePositions_apply
-- name    : Formalism.REAL.permutePositions_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:09:48.332895+00:00
-- url     : https://prove2.me/theorems/1f59bbe6-f2aa-4e64-a8e4-4fadce0be234
-- title:
--   REAL: permute Positions apply
-- statement:
--   The REAL construction uses the permute Positions apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L26-L28

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

theorem Formalism.REAL.permutePositions_apply (σ : Equiv.Perm (Fin j)) (F : Arr V n j) (α : Fin j → Fin n × Fin n) :
    permArr V n σ F α = F (fun i => α (σ i)) := by sorry
