-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_mem_slSpace
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.mem_slSpace
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:58.442674+00:00
-- url     : https://prove2.me/theorems/dbec364c-32be-4402-97e8-84e1c2d648ff
-- title:
--   GS: mem sl Space
-- statement:
--   The GS construction uses the mem sl Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/GenSpace.lean#L77-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/GenSpace.lean#L77-L78

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
variable {k : Type*} [Field k] {σ : Type*}
variable {A B D : Type*} [CommRing A] [CommRing B] [CommRing D] [Algebra k A] [Algebra k B] [Algebra k D]

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.mem_slSpace {P : MvPolynomial σ A} {f : MvPolynomial σ k} :
    f ∈ slSpace (k := k) P ↔ ∃ ℓ : A →ₗ[k] k, slc ℓ P = f := by sorry
