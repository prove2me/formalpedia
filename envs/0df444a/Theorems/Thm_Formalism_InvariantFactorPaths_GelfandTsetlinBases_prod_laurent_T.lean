-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_prod_laurent_T
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.prod_laurent_T
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:23.492541+00:00
-- url     : https://prove2.me/theorems/91e7c9d6-a7dd-4836-b51c-a36d72898b60
-- title:
--   Gelfand Tsetlin Bases: prod laurent T
-- statement:
--   The Gelfand Tsetlin Bases construction uses the prod laurent T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L132-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L132-L137

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.prod_laurent_T {κ : Type*} (s : Finset κ) (f : κ → ℤ) :
    ∏ i ∈ s, (LaurentPolynomial.T (f i) : LaurentPolynomial A) = LaurentPolynomial.T (∑ i ∈ s, f i) := by sorry
