-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_minorF_eq
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.minorF_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:09:07.515257+00:00
-- url     : https://prove2.me/theorems/77b4cd5f-c0f9-42f2-af2b-97c5124cefae
-- title:
--   Gelfand Tsetlin Bases: minor F eq
-- statement:
--   The Gelfand Tsetlin Bases construction uses the minor F eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ActFormContract.lean#L100-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ActFormContract.lean#L100-L105

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
variable {R : Type*} [CommRing R] {n : ℕ}

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.minorF_eq {d : ℕ} (m : Matrix (Fin n) (Fin n) R) {I J : Finset (Fin n)} (hI : I.card = d)
    (hJ : J.card = d) :
    minorF m I J = (m.submatrix (I.orderEmbOfFin hI) (J.orderEmbOfFin hJ)).det := by sorry
