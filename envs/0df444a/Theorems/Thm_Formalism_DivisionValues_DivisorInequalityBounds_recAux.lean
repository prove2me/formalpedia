-- Prove2me | Theorems.Thm_Formalism_DivisionValues_DivisorInequalityBounds_recAux
-- name    : Formalism.DivisionValues.DivisorInequalityBounds.recAux
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:25:45.140212+00:00
-- url     : https://prove2.me/theorems/941b3441-e296-4a37-b52a-ae6ffaef245f
-- title:
--   Divisor Inequality Bounds: rec Aux
-- statement:
--   The Divisor Inequality Bounds construction uses the rec Aux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/GlobalBoundRefinements.lean#L44-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/GlobalBoundRefinements.lean#L44-L56

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

theorem Formalism.DivisionValues.DivisorInequalityBounds.recAux (X B0 Nc m C0 ce Eb lx2 A : ℝ) (hX : 0 < X) (hNc : 0 ≤ Nc)
    (hC0 : 1 ≤ C0) (hce : C0 ≤ ce) (hl : 0 ≤ lx2) (hEb : Eb ≤ ce * m * (X * B0 + lx2 * Nc)) :
    0 ≤ lx2 * Nc / X ∧ X ≤ ce / C0 * X ∧ Eb ≤ C0 * m * (ce / C0 * X) * (B0 + lx2 * Nc / X) ∧
    (50 * C0 + 10) * (A + m * (B0 + lx2 * Nc / X) * (ce / C0 * X)) =
      (50 * C0 + 10) * A + (50 * C0 + 10) * (ce / C0) * (m * (X * B0 + lx2 * Nc)) := by sorry
