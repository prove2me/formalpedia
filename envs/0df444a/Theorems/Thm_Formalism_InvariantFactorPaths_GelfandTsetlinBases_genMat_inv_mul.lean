-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_genMat_inv_mul
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat_inv_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:40:40.583427+00:00
-- url     : https://prove2.me/theorems/5a50d29c-1f8f-443d-a84e-3948455e4f39
-- title:
--   Gelfand Tsetlin Bases: gen Mat inv mul
-- statement:
--   The Gelfand Tsetlin Bases construction uses the gen Mat inv mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L377-L378
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L377-L378

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat_inv_mul (n : ℕ) : (genMat k n)⁻¹ * genMat k n = 1 := by sorry
