-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_lp_supp_C
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.lp_supp_C
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:22.449644+00:00
-- url     : https://prove2.me/theorems/a1ac2fba-8811-4053-a30f-9391e12a16e0
-- title:
--   Gelfand Tsetlin Bases: lp supp C
-- statement:
--   The Gelfand Tsetlin Bases construction uses the lp supp C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L111-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L111-L114

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.lp_supp_C {p : A} (hp : p ≠ 0) :
    (LaurentPolynomial.C p).coeff.support = {0} := by sorry
