-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_map_ant_ant
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.map_ant_ant
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T09:46:43.895359+00:00
-- url     : https://prove2.me/theorems/d8e2d1cf-5ad0-480e-8d19-1022d92176dd
-- title:
--   GS: map ant ant
-- statement:
--   The GS construction uses the map ant ant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/GenSpace.lean#L556-L560
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/GenSpace.lean#L556-L560

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_GenSpaceFacts
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GenSpace
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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
variable {k : Type*} [Field k] {ι ζ : Type*} {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.map_ant_ant (G : MvPolynomial (LVar ι ζ n) k) :
    map (ant k n : UR k n →+* UR k n) (map (ant k n : UR k n →+* UR k n) (rho isVec S G)) = rho isVec S G := by sorry
