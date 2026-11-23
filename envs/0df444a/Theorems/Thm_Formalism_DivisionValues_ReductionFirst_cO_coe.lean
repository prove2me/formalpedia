-- Prove2me | Theorems.Thm_Formalism_DivisionValues_ReductionFirst_cO_coe
-- name    : Formalism.DivisionValues.ReductionFirst.cO_coe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:01:11.382385+00:00
-- url     : https://prove2.me/theorems/08d6097e-f427-44f3-b173-d7063a68be04
-- title:
--   Reduction First: c O coe
-- statement:
--   The Reduction First construction uses the c O coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionLemmaFirst.lean#L30-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionLemmaFirst.lean#L30-L30

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SelectionLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Matrix
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.ReductionFirst
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.DivisionValues.ReductionFirst.cO_coe (x : 𝓞 K) : ((cO K x : 𝓞 K) : K) = star (x : K) := by sorry
