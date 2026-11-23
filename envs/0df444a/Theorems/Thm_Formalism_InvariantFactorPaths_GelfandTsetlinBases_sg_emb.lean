-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_sg_emb
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.sg_emb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:26.717805+00:00
-- url     : https://prove2.me/theorems/42578cc9-354b-4052-9ee6-6d9514378b24
-- title:
--   Gelfand Tsetlin Bases: sg emb
-- statement:
--   The Gelfand Tsetlin Bases construction uses the sg emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ActFormContract.lean#L123-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ActFormContract.lean#L123-L140

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.sg_emb {d : ℕ} {J : Finset (Fin n)} (h : J.card = d + 1) (j : Fin (d + 1)) :
    sg J (J.orderEmbOfFin h j) = (-1) ^ (d + (j : ℕ)) := by sorry
