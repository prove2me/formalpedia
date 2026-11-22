-- Prove2me | Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_vec_zero_of_form
-- name    : Formalism.DivisionValues.FinitelyNonzeroLinear.vec_zero_of_form
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:50:27.634966+00:00
-- url     : https://prove2.me/theorems/1e398ea3-ee03-4938-a41c-049bf7f0c1ac
-- title:
--   Finitely Nonzero Linear: vec zero of form
-- statement:
--   The Finitely Nonzero Linear construction uses the vec zero of form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L517-L521
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L517-L521

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
variable {n : ℕ} {Hc : Matrix (Fin n) (Fin n) ℂ}

theorem Formalism.DivisionValues.FinitelyNonzeroLinear.vec_zero_of_form (hH : Hc.PosDef) (x : Fin n → ℂ) (h : star x ⬝ᵥ Hc *ᵥ x = 0) : x = 0 := by sorry
