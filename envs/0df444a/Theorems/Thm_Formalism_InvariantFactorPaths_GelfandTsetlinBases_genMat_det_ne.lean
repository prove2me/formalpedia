-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_genMat_det_ne
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat_det_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:22:24.155936+00:00
-- url     : https://prove2.me/theorems/6e25b94f-bf0e-400a-9219-b496f99755f0
-- title:
--   Gelfand Tsetlin Bases: gen Mat det ne
-- statement:
--   The Gelfand Tsetlin Bases construction uses the gen Mat det ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L370-L372
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L370-L372

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
variable {ι ζ : Type*} {n : ℕ}
variable (k : Type*) [Field k]

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat_det_ne (n : ℕ) : (genMat k n).det ≠ 0 := by sorry
