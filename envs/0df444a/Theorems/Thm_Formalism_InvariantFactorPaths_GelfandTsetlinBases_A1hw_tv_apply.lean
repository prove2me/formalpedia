-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1hw_tv_apply
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1hw.tv_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:42:06.115337+00:00
-- url     : https://prove2.me/theorems/b8b2a02f-2588-5272-ae51-0d192618fb0e
-- title:
--   A1hw: tv apply
-- statement:
--   The A1hw construction uses the tv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/PathProductHighestWeight.lean#L151-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/PathProductHighestWeight.lean#L151-L153

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1hw.tv_apply {A : Type*} [CommRing A] {n : ℕ} (a b : Fin n) (t : A) (i j : Fin n) :
    Matrix.transvection a b t i j = (if i = j then 1 else 0) + if a = i ∧ b = j then t else 0 := by sorry
