-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_torus_slice
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.torus_slice
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:06:26.603471+00:00
-- url     : https://prove2.me/theorems/9cbe407d-c25a-4a12-86e4-31ff2c1fd797
-- title:
--   GS: torus slice
-- statement:
--   The GS construction uses the torus slice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/GenSpace.lean#L450-L466
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/GenSpace.lean#L450-L466

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
variable {k : Type*} [Field k] [Algebra k A]

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.torus_slice (Q : MvPolynomial (LVar ι ζ n) A) (ν : Fin n → ℤ) :
    slc (cf (k := k) ν) (sharpHom isVec S (dt A n) (dti A n) (map (algebraMap A (TR A n)) Q)) =
      weightedHomogeneousComponent (wV isVec S) ν Q := by sorry
