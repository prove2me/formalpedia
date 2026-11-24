-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_sharp_covec
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.sharp_covec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:43.727189+00:00
-- url     : https://prove2.me/theorems/efa0630a-d5d0-4c7d-8812-e9cef733c6d3
-- title:
--   GS: sharp covec
-- statement:
--   The GS construction uses the sharp covec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/GenSpace.lean#L155-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/GenSpace.lean#L155-L157

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.sharp_covec {i : ι} (h1 : i ∈ S) (h3 : isVec i = false) (g gi : Matrix (Fin n) (Fin n) A) (a : Fin n) :
    sharpHom (ζ := ζ) isVec S g gi (X (Sum.inl (i, a))) = ∑ b, X (Sum.inl (i, b)) * C (gi a b) := by sorry
