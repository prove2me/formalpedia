-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_val_C
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.val_C
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:22.218263+00:00
-- url     : https://prove2.me/theorems/243ce14c-1d1f-4d6a-9047-3d229c738319
-- title:
--   Gelfand Tsetlin Bases: val C
-- statement:
--   The Gelfand Tsetlin Bases construction uses the val C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L402-L405
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L402-L405

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
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
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
variable {ι ζ : Type*} {n : ℕ} {k : Type*} [Field k] (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.val_C {c : k} (hc : c ≠ 0) : valS (ζ := ζ) (n := n) isVec S (C c) = 0 := by sorry
