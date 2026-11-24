-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_sharp_further
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.sharp_further
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:00.538734+00:00
-- url     : https://prove2.me/theorems/5b276471-e4db-42ba-9e23-79aff789e3b7
-- title:
--   GS: sharp further
-- statement:
--   The GS construction uses the sharp further property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/GenSpace.lean#L165-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/GenSpace.lean#L165-L167

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
variable {ι ζ : Type*} {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
variable {A B : Type*} [CommRing A] [CommRing B]
variable {isVec S}
variable (isVec S)

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.sharp_further (g gi : Matrix (Fin n) (Fin n) A) (z : ζ) :
    sharpHom (ι := ι) isVec S g gi (X (Sum.inr z)) = X (Sum.inr z) := by sorry
