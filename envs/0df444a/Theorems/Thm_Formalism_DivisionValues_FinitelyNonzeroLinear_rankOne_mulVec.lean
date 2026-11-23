-- Prove2me | Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_rankOne_mulVec
-- name    : Formalism.DivisionValues.FinitelyNonzeroLinear.rankOne_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:10.457126+00:00
-- url     : https://prove2.me/theorems/c7ca2d7f-a14b-4940-85cb-0e95ac534f62
-- title:
--   Finitely Nonzero Linear: rank One mul Vec
-- statement:
--   The Finitely Nonzero Linear construction uses the rank One mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L663-L669
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean#L663-L669

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

theorem Formalism.DivisionValues.FinitelyNonzeroLinear.rankOne_mulVec (x y v : Fin n → ℂ) :
    rankOne Hc x y *ᵥ v = (star x ⬝ᵥ Hc *ᵥ v) • y := by sorry
