-- Prove2me | Theorems.Thm_Formalism_DivisionValues_W5_aux_statement_15
-- name    : Formalism.DivisionValues.W5.aux_statement_15
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:20:44.272649+00:00
-- url     : https://prove2.me/theorems/6a8680e5-693e-4de7-9cb4-a3986c330a4c
-- title:
--   W5: aux statement 15
-- statement:
--   The W5 construction uses the aux statement 15 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/PlaceSumSquares.lean#L249-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/PlaceSumSquares.lean#L249-L256

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

theorem Formalism.DivisionValues.W5.aux_statement_15 (p : ℕ) (hp : p.Prime) (h : 240 ≤ p) : p % 6 = 1 ∨ p % 6 = 5 := by sorry
