-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_prod_single
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.prod_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:50.476336+00:00
-- url     : https://prove2.me/theorems/1503ae80-3902-41fe-b016-c719b1ed786a
-- title:
--   GS: prod single
-- statement:
--   The GS construction uses the prod single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/GenSpace.lean#L425-L432
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/GenSpace.lean#L425-L432

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
variable (A : Type*) [CommRing A]
variable {A}

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.prod_single {κ M : Type*} [AddCommMonoid M] (s : Finset κ) (f : κ → M) :
    ∏ x ∈ s, (AddMonoidAlgebra.single (f x) (1 : A) : AddMonoidAlgebra A M) =
      AddMonoidAlgebra.single (∑ x ∈ s, f x) 1 := by sorry
