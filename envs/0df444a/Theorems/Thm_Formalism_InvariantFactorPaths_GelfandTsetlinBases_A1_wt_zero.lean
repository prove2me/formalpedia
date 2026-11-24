-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_wt_zero
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.wt_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:34:09.910994+00:00
-- url     : https://prove2.me/theorems/928dbb01-1174-47bd-adb2-7ee3e3a086a4
-- title:
--   A1: wt zero
-- statement:
--   The A1 construction uses the wt zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/IsWeightedHomogeneousZeroStripPathWord.lean#L153-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/IsWeightedHomogeneousZeroStripPathWord.lean#L153-L160

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.wt_zero {n N : ℕ} (v : Bool) {x : ℕ × Fin n} (hx : x.1 ≠ N) : wt n N v x = 0 := by sorry
