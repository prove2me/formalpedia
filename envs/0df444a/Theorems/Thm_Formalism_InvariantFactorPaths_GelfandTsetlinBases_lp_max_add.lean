-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_lp_max_add
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.lp_max_add
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:04.35753+00:00
-- url     : https://prove2.me/theorems/e56b0e4c-e9bc-4056-89b5-596ef75594e7
-- title:
--   Gelfand Tsetlin Bases: lp max add
-- statement:
--   The Gelfand Tsetlin Bases construction uses the lp max add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L95-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L95-L103

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
omit [IsDomain A]

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.lp_max_add (x y : LaurentPolynomial A) :
    (x + y).coeff.support.max ≤ max x.coeff.support.max y.coeff.support.max := by sorry
