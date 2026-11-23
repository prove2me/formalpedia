-- Prove2me | Theorems.Thm_Formalism_DivisionValues_W5_blk
-- name    : Formalism.DivisionValues.W5.blk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:20:58.044902+00:00
-- url     : https://prove2.me/theorems/3a232723-7b92-471f-bc17-601a412a097a
-- title:
--   W5: blk
-- statement:
--   The W5 construction uses the blk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/PlaceSumSquares.lean#L211-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/PlaceSumSquares.lean#L211-L247

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

theorem Formalism.DivisionValues.W5.blk (K : ℕ) (hK : 40 ≤ K) :
    ∑ n ∈ Finset.Ico 240 (6 * K),
      (if n % 6 = 1 ∨ n % 6 = 5 then Real.log (n : ℝ) / (n : ℝ) ^ 2 else 0) ≤
    ((Real.log 234 + 1) / 234 - (Real.log ((6 * K : ℕ) - 6 : ℝ) + 1) / ((6 * K : ℕ) - 6 : ℝ)) / 3 := by sorry
