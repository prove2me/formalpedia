-- Prove2me | Theorems.Thm_Formalism_DivisionValues_ReductionFirst_cO_cO
-- name    : Formalism.DivisionValues.ReductionFirst.cO_cO
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:45.722578+00:00
-- url     : https://prove2.me/theorems/43810c78-8da1-4a52-91a4-f2ec0e020676
-- title:
--   Reduction First: c O c O
-- statement:
--   The Reduction First construction uses the c O c O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionLemmaFirst.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionLemmaFirst.lean#L32-L34

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

theorem Formalism.DivisionValues.ReductionFirst.cO_cO (x : 𝓞 K) : cO K (cO K x) = x := by sorry
