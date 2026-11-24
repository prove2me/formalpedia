-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_map_nonsing_inv
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.map_nonsing_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:51.48293+00:00
-- url     : https://prove2.me/theorems/35d4324d-f571-43bd-acdc-35114a75ed29
-- title:
--   GS: map nonsing inv
-- statement:
--   The GS construction uses the map nonsing inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/GenSpace.lean#L210-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/GenSpace.lean#L210-L215

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.map_nonsing_inv {A B : Type*} [CommRing A] [CommRing B] {n : ℕ} (f : A →+* B)
    (m : Matrix (Fin n) (Fin n) A) (hm : IsUnit m.det) : (m⁻¹).map f = (m.map f)⁻¹ := by sorry
