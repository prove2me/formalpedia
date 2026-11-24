-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_sharp_comp
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.sharp_comp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:55:16.895807+00:00
-- url     : https://prove2.me/theorems/5ef6b2bb-330e-426d-838a-d660fea9cf58
-- title:
--   GS: sharp comp
-- statement:
--   The GS construction uses the sharp comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/GenSpace.lean#L185-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/GenSpace.lean#L185-L204

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.sharp_comp (x xi y yi : Matrix (Fin n) (Fin n) A) (P : MvPolynomial (LVar ι ζ n) A) :
    sharpHom isVec S x xi (sharpHom isVec S y yi P) = sharpHom isVec S (x * y) (yi * xi) P := by sorry
