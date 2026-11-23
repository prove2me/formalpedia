-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_emb_succAbove
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.emb_succAbove
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:56:39.616801+00:00
-- url     : https://prove2.me/theorems/a0fb04ec-6ad5-46f1-834d-5c678f626acc
-- title:
--   Gelfand Tsetlin Bases: emb succ Above
-- statement:
--   The Gelfand Tsetlin Bases construction uses the emb succ Above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ActFormContract.lean#L112-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ActFormContract.lean#L112-L121

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.emb_succAbove {d : ℕ} {J J' : Finset (Fin n)} (h : J.card = d + 1) (j : Fin (d + 1))
    (hJ' : J' = J.erase (J.orderEmbOfFin h j)) (h' : J'.card = d) :
    (fun x => J.orderEmbOfFin h (j.succAbove x)) = J'.orderEmbOfFin h' := by sorry
