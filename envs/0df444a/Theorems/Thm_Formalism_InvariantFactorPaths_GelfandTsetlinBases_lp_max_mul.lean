-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_lp_max_mul
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.lp_max_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:43.069724+00:00
-- url     : https://prove2.me/theorems/38a6cc5d-07a2-4833-b9f3-81daaa19de22
-- title:
--   Gelfand Tsetlin Bases: lp max mul
-- statement:
--   The Gelfand Tsetlin Bases construction uses the lp max mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L51-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L51-L81

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.lp_max_mul (x y : LaurentPolynomial A) :
    (x * y).coeff.support.max = x.coeff.support.max + y.coeff.support.max := by sorry
