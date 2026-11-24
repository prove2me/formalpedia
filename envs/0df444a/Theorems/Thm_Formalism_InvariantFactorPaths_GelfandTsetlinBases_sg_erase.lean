-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_sg_erase
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.sg_erase
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:34.82647+00:00
-- url     : https://prove2.me/theorems/1a438df0-ebb8-4940-b9b6-3545dfe53d23
-- title:
--   Gelfand Tsetlin Bases: sg erase
-- statement:
--   The Gelfand Tsetlin Bases construction uses the sg erase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ActFormContract.lean#L32-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ActFormContract.lean#L32-L43

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.sg_erase {I : Finset (Fin n)} {m' : Fin n} (hm' : m' ∈ I) (m : Fin n) :
    sg (I.erase m') m = sg I m * (if m < m' then -1 else 1) := by sorry
