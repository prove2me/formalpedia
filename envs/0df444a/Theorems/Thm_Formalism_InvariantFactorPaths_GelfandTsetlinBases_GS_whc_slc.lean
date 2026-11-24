-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_whc_slc
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.whc_slc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:55:35.565674+00:00
-- url     : https://prove2.me/theorems/31a018fc-d44b-44cd-aa57-6765a9e1a96b
-- title:
--   GS: whc slc
-- statement:
--   The GS construction uses the whc slc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/GenSpace.lean#L468-L474
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/GenSpace.lean#L468-L474

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.whc_slc (ℓ : A →ₗ[k] k) (P : MvPolynomial (LVar ι ζ n) A) (ν : Fin n → ℤ) :
    weightedHomogeneousComponent (wV isVec S) ν (slc ℓ P) =
      slc ℓ (weightedHomogeneousComponent (wV isVec S) ν P) := by sorry
