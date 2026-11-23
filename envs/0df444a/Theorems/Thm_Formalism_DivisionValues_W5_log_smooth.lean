-- Prove2me | Theorems.Thm_Formalism_DivisionValues_W5_log_smooth
-- name    : Formalism.DivisionValues.W5.log_smooth
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:06.606849+00:00
-- url     : https://prove2.me/theorems/3a1eb9ad-1c2d-4dcf-aab3-93c81ec11681
-- title:
--   W5: log smooth
-- statement:
--   The W5 construction uses the log smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/PlaceSumSquares.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/PlaceSumSquares.lean#L21-L26

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

theorem Formalism.DivisionValues.W5.log_smooth (a b c d : ℕ) :
    Real.log ((2 : ℝ) ^ a * 3 ^ b * 5 ^ c * 7 ^ d) =
      a * Real.log 2 + b * Real.log 3 + c * Real.log 5 + d * Real.log 7 := by sorry
