-- Prove2me | Theorems.Thm_Formalism_DivisionValues_prime_mod_six_of_large
-- name    : Formalism.DivisionValues.prime_mod_six_of_large
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:00.17091+00:00
-- url     : https://prove2.me/theorems/a64c4e82-6ff8-4cb4-8bad-02b8a777809b
-- title:
--   Division Values: prime mod six of large
-- statement:
--   The Division Values construction uses the prime mod six of large property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/PlaceSumSquares.lean#L303-L327
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/PlaceSumSquares.lean#L303-L327

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

theorem Formalism.DivisionValues.prime_mod_six_of_large : PrimeSumSq := by sorry
