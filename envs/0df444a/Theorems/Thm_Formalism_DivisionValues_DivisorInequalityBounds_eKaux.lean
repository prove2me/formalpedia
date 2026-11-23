-- Prove2me | Theorems.Thm_Formalism_DivisionValues_DivisorInequalityBounds_eKaux
-- name    : Formalism.DivisionValues.DivisorInequalityBounds.eKaux
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:01.51235+00:00
-- url     : https://prove2.me/theorems/1dab6023-7f8e-4b2f-b95b-ee8b609a5187
-- title:
--   Divisor Inequality Bounds: e Kaux
-- statement:
--   The Divisor Inequality Bounds construction uses the e Kaux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/GlobalBoundRefinements.lean#L36-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/GlobalBoundRefinements.lean#L36-L42

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ScalarLiftLowerBoundFull
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_PlaceSumSquares
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_WeightedPlaceLogSum
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_GlobalBoundRefinements
import Theorems.Thm_Formalism_DivisionValues_WeightedPlaceLogSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.DivisorInequalityBounds

theorem Formalism.DivisionValues.DivisorInequalityBounds.eKaux (C0 f N La m L e : ℝ) (hC0 : 1 ≤ C0) (hf : 1 ≤ f) (hN : 1 ≤ N)
    (h : e ≤ C0 * (f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L)) :
    e ≤ C0 * (f * N ^ 2 * (La + 1) + f * m ^ 3 * N ^ 2 * L) := by sorry
