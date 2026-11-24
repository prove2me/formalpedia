-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_sgR_mul_self
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.sgR_mul_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:28.27026+00:00
-- url     : https://prove2.me/theorems/f1e0e88a-1721-4bd1-ac41-c3a65a2e3e50
-- title:
--   Gelfand Tsetlin Bases: sg R mul self
-- statement:
--   The Gelfand Tsetlin Bases construction uses the sg R mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ActFormContract.lean#L45-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ActFormContract.lean#L45-L46

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.sgR_mul_self (I : Finset (Fin n)) (m : Fin n) : ((sg I m : ℤ) : R) * ((sg I m : ℤ) : R) = 1 := by sorry
