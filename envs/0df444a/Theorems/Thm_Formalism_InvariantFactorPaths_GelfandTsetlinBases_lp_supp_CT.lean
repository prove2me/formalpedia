-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_lp_supp_CT
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.lp_supp_CT
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:06.67331+00:00
-- url     : https://prove2.me/theorems/82f1fe0c-4174-4458-ac57-296a3cc3fdea
-- title:
--   Gelfand Tsetlin Bases: lp supp CT
-- statement:
--   The Gelfand Tsetlin Bases construction uses the lp supp CT property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L106-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L106-L108

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.lp_supp_CT {p : A} (hp : p ≠ 0) (m : ℤ) :
    (LaurentPolynomial.C p * LaurentPolynomial.T m).coeff.support = {m} := by sorry
