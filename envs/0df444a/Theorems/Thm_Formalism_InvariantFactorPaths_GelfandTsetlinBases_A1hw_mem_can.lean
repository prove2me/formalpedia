-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1hw_mem_can
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1hw.mem_can
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:34:24.691793+00:00
-- url     : https://prove2.me/theorems/5d60d080-d1f6-4bcf-b251-4263d5ade511
-- title:
--   A1hw: mem can
-- statement:
--   The A1hw construction uses the mem can property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/PathProductHighestWeight.lean#L68-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/PathProductHighestWeight.lean#L68-L75

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
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
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1hw

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1hw.mem_can {n : ℕ} {μN : Fin n → ℤ} (h : Antitone μN) (c : ℤ) (m : Fin n) :
    m ∈ canIdx μN c ↔ if 1 ≤ c then c ≤ μN m else μN m < c := by sorry
