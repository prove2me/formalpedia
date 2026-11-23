-- Prove2me | Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_fnl_extSpan
-- name    : Formalism.DivisionValues.FinitelyNonzeroLinear.fnl_extSpan
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:10.150345+00:00
-- url     : https://prove2.me/theorems/1909214a-0af2-4ba2-a329-2cdf7f8622dc
-- title:
--   Finitely Nonzero Linear: fnl ext Span
-- statement:
--   The Finitely Nonzero Linear construction uses the fnl ext Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L120-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L120-L154

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

theorem Formalism.DivisionValues.FinitelyNonzeroLinear.fnl_extSpan {n : ℕ} (Z : Submodule K (Fin n → K)) (y : Fin n → Ω)
    (hy : y ∈ extSpan j Z) : ∀ ρ : Fnl j, (fun i => ρ.toFun (y i)) ∈ Z := by sorry
