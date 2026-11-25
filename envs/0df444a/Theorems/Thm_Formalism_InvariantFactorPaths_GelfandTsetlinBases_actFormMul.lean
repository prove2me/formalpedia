-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_actFormMul
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.actFormMul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:41:52.128847+00:00
-- url     : https://prove2.me/theorems/6c6d0d9b-3c92-466c-8665-e3b8c07c235d
-- title:
--   Gelfand Tsetlin Bases: act Form Mul
-- statement:
--   The Gelfand Tsetlin Bases construction uses the act Form Mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ActFormContract.lean#L372-L398
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ActFormContract.lean#L372-L398

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.actFormMul : FactX2mul := by sorry
