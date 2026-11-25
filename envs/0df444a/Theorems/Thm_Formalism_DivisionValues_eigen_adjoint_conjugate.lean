-- Prove2me | Theorems.Thm_Formalism_DivisionValues_eigen_adjoint_conjugate
-- name    : Formalism.DivisionValues.eigen_adjoint_conjugate
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:26:50.961455+00:00
-- url     : https://prove2.me/theorems/4afffa8a-71db-4dc3-b781-a68fdbb75c69
-- title:
--   Division Values: eigen adjoint conjugate
-- statement:
--   The Division Values construction uses the eigen adjoint conjugate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L780-L792
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L780-L792

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_EigenRatHermLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open FinitelyNonzeroLinear

theorem Formalism.DivisionValues.eigen_adjoint_conjugate : EigenAdjConj := by sorry
