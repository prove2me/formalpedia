-- Prove2me | Theorems.Thm_Formalism_DivisionValues_W5_head_sum
-- name    : Formalism.DivisionValues.W5.head_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:20:45.429216+00:00
-- url     : https://prove2.me/theorems/026ed47f-3a0f-4410-a8b7-fa93d123c686
-- title:
--   W5: head sum
-- statement:
--   The W5 construction uses the head sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/PlaceSumSquares.lean#L160-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/PlaceSumSquares.lean#L160-L164

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_UntwistedChoice
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_PlaceSumSquares
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
open Formalism.DivisionValues.W5
set_option maxRecDepth 100000

theorem Formalism.DivisionValues.W5.head_sum :
    ∑ n ∈ Finset.range 240, (if n.Prime then Real.log (n : ℝ) / (n : ℝ) ^ 2 else 0) =
    Real.log 2 / 2 ^ 2 + Real.log 3 / 3 ^ 2 + Real.log 5 / 5 ^ 2 + Real.log 7 / 7 ^ 2 + Real.log 11 / 11 ^ 2 + Real.log 13 / 13 ^ 2 + Real.log 17 / 17 ^ 2 + Real.log 19 / 19 ^ 2 + Real.log 23 / 23 ^ 2 + Real.log 29 / 29 ^ 2 + Real.log 31 / 31 ^ 2 + Real.log 37 / 37 ^ 2 + Real.log 41 / 41 ^ 2 + Real.log 43 / 43 ^ 2 + Real.log 47 / 47 ^ 2 + Real.log 53 / 53 ^ 2 + Real.log 59 / 59 ^ 2 + Real.log 61 / 61 ^ 2 + Real.log 67 / 67 ^ 2 + Real.log 71 / 71 ^ 2 + Real.log 73 / 73 ^ 2 + Real.log 79 / 79 ^ 2 + Real.log 83 / 83 ^ 2 + Real.log 89 / 89 ^ 2 + Real.log 97 / 97 ^ 2 + Real.log 101 / 101 ^ 2 + Real.log 103 / 103 ^ 2 + Real.log 107 / 107 ^ 2 + Real.log 109 / 109 ^ 2 + Real.log 113 / 113 ^ 2 + Real.log 127 / 127 ^ 2 + Real.log 131 / 131 ^ 2 + Real.log 137 / 137 ^ 2 + Real.log 139 / 139 ^ 2 + Real.log 149 / 149 ^ 2 + Real.log 151 / 151 ^ 2 + Real.log 157 / 157 ^ 2 + Real.log 163 / 163 ^ 2 + Real.log 167 / 167 ^ 2 + Real.log 173 / 173 ^ 2 + Real.log 179 / 179 ^ 2 + Real.log 181 / 181 ^ 2 + Real.log 191 / 191 ^ 2 + Real.log 193 / 193 ^ 2 + Real.log 197 / 197 ^ 2 + Real.log 199 / 199 ^ 2 + Real.log 211 / 211 ^ 2 + Real.log 223 / 223 ^ 2 + Real.log 227 / 227 ^ 2 + Real.log 229 / 229 ^ 2 + Real.log 233 / 233 ^ 2 + Real.log 239 / 239 ^ 2 := by sorry
