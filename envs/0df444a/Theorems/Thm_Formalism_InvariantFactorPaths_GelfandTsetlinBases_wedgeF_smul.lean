-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_wedgeF_smul
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.wedgeF_smul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:41:56.155511+00:00
-- url     : https://prove2.me/theorems/550dd32e-5708-51eb-a09f-ed3bd1861ff5
-- title:
--   Gelfand Tsetlin Bases: wedge F smul
-- statement:
--   The Gelfand Tsetlin Bases construction uses the wedge F smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ActFormContract.lean#L234-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ActFormContract.lean#L234-L240

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.wedgeF_smul (c : R) (K : Form R n) (X : Fin n → R) :
    wedgeF (c • K) X = c • wedgeF K X := by sorry
