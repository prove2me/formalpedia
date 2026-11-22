-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_actF_oneF
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.actF_oneF
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:08:50.447349+00:00
-- url     : https://prove2.me/theorems/8d3450cc-6a2b-4f05-8afc-1aa42ac12dba
-- title:
--   Gelfand Tsetlin Bases: act F one F
-- statement:
--   The Gelfand Tsetlin Bases construction uses the act F one F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ActFormContract.lean#L353-L362
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ActFormContract.lean#L353-L362

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.actF_oneF (m : Matrix (Fin n) (Fin n) R) : actF (oneF : Form R n) m = oneF := by sorry
