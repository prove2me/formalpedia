-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_SignTwistStarLemmas_jacobi_gen
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas.jacobi_gen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:06:30.868931+00:00
-- url     : https://prove2.me/theorems/deea7522-18c3-4cd5-8f3e-5fc5026eec8e
-- title:
--   Sign Twist Star Lemmas: jacobi gen
-- statement:
--   The Sign Twist Star Lemmas construction uses the jacobi gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/JacobiMinorProof.lean#L108-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/JacobiMinorProof.lean#L108-L117

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_JacobiMinorProof
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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas
variable {R : Type} [CommRing R] {n : ℕ}

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas.jacobi_gen (m : (Matrix (Fin n) (Fin n) R)ˣ) (I J : Finset (Fin n)) :
    (↑m : Matrix (Fin n) (Fin n) R).det * minorF (↑m⁻¹ : Matrix (Fin n) (Fin n) R).transpose I J =
      (-1) ^ (epsN Iᶜ + epsN Jᶜ) * minorF (↑m : Matrix (Fin n) (Fin n) R) Iᶜ Jᶜ := by sorry
