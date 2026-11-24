-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_lp_coeff_TC
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.lp_coeff_TC
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:51.976389+00:00
-- url     : https://prove2.me/theorems/7d36d516-4c25-4012-a2ba-6995f3bd1021
-- title:
--   Gelfand Tsetlin Bases: lp coeff TC
-- statement:
--   The Gelfand Tsetlin Bases construction uses the lp coeff TC property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L117-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L117-L120

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.lp_coeff_TC (p : A) (m j : ℤ) :
    (LaurentPolynomial.T m * LaurentPolynomial.C p).coeff j = if m = j then p else 0 := by sorry
