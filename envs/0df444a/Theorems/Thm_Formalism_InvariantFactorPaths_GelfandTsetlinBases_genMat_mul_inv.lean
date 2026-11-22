-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_genMat_mul_inv
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat_mul_inv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:40:34.227056+00:00
-- url     : https://prove2.me/theorems/50b41f12-6b06-4838-8db1-78fe8247418d
-- title:
--   Gelfand Tsetlin Bases: gen Mat mul inv
-- statement:
--   The Gelfand Tsetlin Bases construction uses the gen Mat mul inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L374-L375
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L374-L375

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat_mul_inv (n : ℕ) : genMat k n * (genMat k n)⁻¹ = 1 := by sorry
