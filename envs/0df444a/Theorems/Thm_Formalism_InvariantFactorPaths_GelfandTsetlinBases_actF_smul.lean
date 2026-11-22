-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_actF_smul
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.actF_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:09:16.14167+00:00
-- url     : https://prove2.me/theorems/42118579-9b02-4b9c-a0ca-813a21bdfe83
-- title:
--   Gelfand Tsetlin Bases: act F smul
-- statement:
--   The Gelfand Tsetlin Bases construction uses the act F smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ActFormContract.lean#L219-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ActFormContract.lean#L219-L222

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.actF_smul (c : R) (K : Form R n) (m : Matrix (Fin n) (Fin n) R) :
    actF (c • K) m = c • actF K m := by sorry
