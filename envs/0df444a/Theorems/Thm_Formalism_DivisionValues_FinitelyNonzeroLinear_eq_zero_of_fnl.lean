-- Prove2me | Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_eq_zero_of_fnl
-- name    : Formalism.DivisionValues.FinitelyNonzeroLinear.eq_zero_of_fnl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:08.043886+00:00
-- url     : https://prove2.me/theorems/b32c79ab-0c24-483b-ab15-7de2e3068e3b
-- title:
--   Finitely Nonzero Linear: eq zero of fnl
-- statement:
--   The Finitely Nonzero Linear construction uses the eq zero of fnl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L99-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L99-L103

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
variable (j)

theorem Formalism.DivisionValues.FinitelyNonzeroLinear.eq_zero_of_fnl (c : Ω) (h : ∀ ρ : Fnl j, ρ.toFun c = 0) : c = 0 := by sorry
