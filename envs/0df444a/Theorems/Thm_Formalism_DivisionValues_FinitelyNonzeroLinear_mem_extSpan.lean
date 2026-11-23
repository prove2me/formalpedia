-- Prove2me | Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_mem_extSpan
-- name    : Formalism.DivisionValues.FinitelyNonzeroLinear.mem_extSpan
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:56:37.946243+00:00
-- url     : https://prove2.me/theorems/533fed43-6210-46d7-88ab-b833db690e47
-- title:
--   Finitely Nonzero Linear: mem ext Span
-- statement:
--   The Finitely Nonzero Linear construction uses the mem ext Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L161-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L161-L164

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

theorem Formalism.DivisionValues.FinitelyNonzeroLinear.mem_extSpan {n : ℕ} {Z : Submodule K (Fin n → K)} {z : Fin n → K} (hz : z ∈ Z) :
    (fun i => j (z i)) ∈ extSpan j Z := by sorry
