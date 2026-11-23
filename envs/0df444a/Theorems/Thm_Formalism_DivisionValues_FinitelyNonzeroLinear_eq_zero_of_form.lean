-- Prove2me | Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_eq_zero_of_form
-- name    : Formalism.DivisionValues.FinitelyNonzeroLinear.eq_zero_of_form
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:14.572337+00:00
-- url     : https://prove2.me/theorems/5565a6e3-e6a6-45b2-ad5b-cdbeeb393d41
-- title:
--   Finitely Nonzero Linear: eq zero of form
-- statement:
--   The Finitely Nonzero Linear construction uses the eq zero of form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L14-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L14-L27

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

theorem Formalism.DivisionValues.FinitelyNonzeroLinear.eq_zero_of_form {n m : ℕ} {Hc : Matrix (Fin n) (Fin n) ℂ} (hH : Hc.PosDef)
    (F : Matrix (Fin n) (Fin m) ℂ) (h : Fᴴ * Hc * F = 0) : F = 0 := by sorry
