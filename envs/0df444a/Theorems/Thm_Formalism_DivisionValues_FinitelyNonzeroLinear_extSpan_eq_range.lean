-- Prove2me | Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_extSpan_eq_range
-- name    : Formalism.DivisionValues.FinitelyNonzeroLinear.extSpan_eq_range
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:56:12.131927+00:00
-- url     : https://prove2.me/theorems/f654a03f-9130-4d2c-af43-2018a8789f3e
-- title:
--   Finitely Nonzero Linear: ext Span eq range
-- statement:
--   The Finitely Nonzero Linear construction uses the ext Span eq range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L166-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L166-L186

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

theorem Formalism.DivisionValues.FinitelyNonzeroLinear.extSpan_eq_range {n : ℕ} (Z : Submodule K (Fin n → K)) (e : Matrix (Fin n) (Fin n) K)
    (h1 : ∀ x, e *ᵥ x ∈ Z) (h2 : ∀ z ∈ Z, e *ᵥ z = z) :
    extSpan j Z = LinearMap.range (e.map j).mulVecLin := by sorry
