-- Prove2me | Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_Fnl_zero
-- name    : Formalism.DivisionValues.FinitelyNonzeroLinear.Fnl.zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:49:08.888799+00:00
-- url     : https://prove2.me/theorems/9f9baaf8-8663-4226-b788-80ca0a9aeeea
-- title:
--   Fnl: zero
-- statement:
--   The Fnl construction uses the zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L83-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L83-L84

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
open Formalism.DivisionValues.FinitelyNonzeroLinear
variable {K Ω : Type} [Field K] [Field Ω] (j : K →+* Ω)
variable {j}

theorem Formalism.DivisionValues.FinitelyNonzeroLinear.Fnl.zero (ρ : Fnl j) : ρ.toFun 0 = 0 := by sorry
