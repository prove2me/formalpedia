-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_genMat_eq
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:54.909803+00:00
-- url     : https://prove2.me/theorems/658f153d-5e6a-4f71-9c87-0909100dc4c5
-- title:
--   Gelfand Tsetlin Bases: gen Mat eq
-- statement:
--   The Gelfand Tsetlin Bases construction uses the gen Mat eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L365-L368
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L365-L368

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat_eq (n : ℕ) : genMat k n =
    (algebraMap (MvPolynomial (Fin n × Fin n) k) (GenField k n)).mapMatrix (Matrix.mvPolynomialX (Fin n) (Fin n) k) := by sorry
