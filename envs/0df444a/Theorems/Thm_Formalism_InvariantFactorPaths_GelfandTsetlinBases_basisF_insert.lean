-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_basisF_insert
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.basisF_insert
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:43.217337+00:00
-- url     : https://prove2.me/theorems/10246f2a-9974-4b09-b14f-934dfd488dfb
-- title:
--   Gelfand Tsetlin Bases: basis F insert
-- statement:
--   The Gelfand Tsetlin Bases construction uses the basis F insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ActFormContract.lean#L308-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ActFormContract.lean#L308-L334

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.basisF_insert {a : Fin n} {s : Finset (Fin n)} (hs : ∀ x ∈ s, x < a) :
    (basisF (insert a s) : Form R n) = wedgeF (basisF s) (Pi.single a 1) := by sorry
