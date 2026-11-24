-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_lp_min_mul
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.lp_min_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:07.591105+00:00
-- url     : https://prove2.me/theorems/8dbdc1aa-74c0-4878-8013-0fdf642b0dc9
-- title:
--   Gelfand Tsetlin Bases: lp min mul
-- statement:
--   The Gelfand Tsetlin Bases construction uses the lp min mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L19-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L19-L49

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
variable {A : Type*} [CommRing A] [IsDomain A]

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.lp_min_mul (x y : LaurentPolynomial A) :
    (x * y).coeff.support.min = x.coeff.support.min + y.coeff.support.min := by sorry
