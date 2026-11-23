-- Prove2me | Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_eq_of_fnl
-- name    : Formalism.DivisionValues.FinitelyNonzeroLinear.eq_of_fnl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:13:25.556124+00:00
-- url     : https://prove2.me/theorems/61e5908c-943e-49d6-b23f-015d2abf5aa6
-- title:
--   Finitely Nonzero Linear: eq of fnl
-- statement:
--   The Finitely Nonzero Linear construction uses the eq of fnl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L223-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L223-L229

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

theorem Formalism.DivisionValues.FinitelyNonzeroLinear.eq_of_fnl {K Ω : Type} [Field K] [Field Ω] (j : K →+* Ω) (c c' : Ω)
    (h : ∀ ρ : Fnl j, ρ.toFun c = ρ.toFun c') : c = c' := by sorry
