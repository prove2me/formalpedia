-- Prove2me | Theorems.Thm_Formalism_DivisionValues_full_eigen_commuting
-- name    : Formalism.DivisionValues.full_eigen_commuting
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:34.842808+00:00
-- url     : https://prove2.me/theorems/6558f37d-86f8-465a-b14e-c7113f1d6c3e
-- title:
--   Division Values: full eigen commuting
-- statement:
--   The Division Values construction uses the full eigen commuting property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L193-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L193-L219

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

theorem Formalism.DivisionValues.full_eigen_commuting : FullEigComm := by sorry
