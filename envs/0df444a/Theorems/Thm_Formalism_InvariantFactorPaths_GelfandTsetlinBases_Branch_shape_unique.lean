-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Branch_shape_unique
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.shape_unique
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:07.323088+00:00
-- url     : https://prove2.me/theorems/0b81cbe9-ffff-448a-b52d-eaf1c9e84f22
-- title:
--   Branch: shape unique
-- statement:
--   The Branch construction uses the shape unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/Branch.lean#L266-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/Branch.lean#L266-L271

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_Branch
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.shape_unique {n : ℕ} {κ κ' : Fin n → ℤ} (h : Antitone κ) (h' : Antitone κ')
    (he : ∀ c, colHeight κ c = colHeight κ' c) : κ = κ' := by sorry
