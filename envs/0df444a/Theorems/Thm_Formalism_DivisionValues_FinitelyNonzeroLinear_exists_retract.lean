-- Prove2me | Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_exists_retract
-- name    : Formalism.DivisionValues.FinitelyNonzeroLinear.exists_retract
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:06.672374+00:00
-- url     : https://prove2.me/theorems/3086b034-83a5-45ad-8c03-4835ab86cd90
-- title:
--   Finitely Nonzero Linear: exists retract
-- statement:
--   The Finitely Nonzero Linear construction uses the exists retract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L91-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L91-L96

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

theorem Formalism.DivisionValues.FinitelyNonzeroLinear.exists_retract : ∃ ρ : Fnl j, ∀ a, ρ.toFun (j a) = a := by sorry
