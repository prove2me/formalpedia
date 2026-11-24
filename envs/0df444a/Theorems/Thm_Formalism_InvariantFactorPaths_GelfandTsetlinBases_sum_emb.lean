-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_sum_emb
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.sum_emb
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:56.755646+00:00
-- url     : https://prove2.me/theorems/e4d89ab7-4b34-42f7-9ead-40e6e86d7e84
-- title:
--   Gelfand Tsetlin Bases: sum emb
-- statement:
--   The Gelfand Tsetlin Bases construction uses the sum emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ActFormContract.lean#L142-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ActFormContract.lean#L142-L145

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.sum_emb {d : ℕ} {J : Finset (Fin n)} (h : J.card = d) (f : Fin n → R) :
    ∑ b ∈ J, f b = ∑ j, f (J.orderEmbOfFin h j) := by sorry
