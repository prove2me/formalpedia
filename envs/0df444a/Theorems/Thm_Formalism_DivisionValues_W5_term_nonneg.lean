-- Prove2me | Theorems.Thm_Formalism_DivisionValues_W5_term_nonneg
-- name    : Formalism.DivisionValues.W5.term_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:22:58.785794+00:00
-- url     : https://prove2.me/theorems/659ba57f-3e4c-4540-bc40-93ddd714b413
-- title:
--   W5: term nonneg
-- statement:
--   The W5 construction uses the term nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/PlaceSumSquares.lean#L258-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/PlaceSumSquares.lean#L258-L259

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

theorem Formalism.DivisionValues.W5.term_nonneg (n : ℕ) : 0 ≤ Real.log (n : ℝ) / (n : ℝ) ^ 2 := by sorry
