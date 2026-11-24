-- Prove2me | Theorems.Thm_Formalism_DivisionValues_ReductionFirst_smul_coe
-- name    : Formalism.DivisionValues.ReductionFirst.smul_coe
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:05:06.791182+00:00
-- url     : https://prove2.me/theorems/c872d713-4e56-4913-bded-2e1cc09844d2
-- title:
--   Reduction First: smul coe
-- statement:
--   The Reduction First construction uses the smul coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionLemmaFirst.lean#L45-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionLemmaFirst.lean#L45-L46

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

theorem Formalism.DivisionValues.ReductionFirst.smul_coe {m : Type*} (r : 𝓞 K) (v : m → K) : r • v = (r : K) • v := by sorry
