-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_uAlg_algebraMap
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.uAlg_algebraMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:06.845292+00:00
-- url     : https://prove2.me/theorems/dd3a9754-dc31-444c-809f-feb0ce08eaa3
-- title:
--   GS: u Alg algebra Map
-- statement:
--   The GS construction uses the u Alg algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/GenSpace.lean#L252-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/GenSpace.lean#L252-L255

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
variable (k : Type*) [Field k] (n : ℕ)
variable {k n}
variable {B : Type*} [CommRing B] [Algebra k B]

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.uAlg_algebraMap (g₀ : Matrix (Fin n) (Fin n) B) (h : IsUnit g₀.det)
    (x : MvPolynomial (Fin n × Fin n) k) :
    uAlg k g₀ h (algebraMap _ _ x) = aeval (fun p : Fin n × Fin n => g₀ p.1 p.2) x := by sorry
