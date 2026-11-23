-- Prove2me | Theorems.Thm_Formalism_DivisionValues_ReductionFirst_cO_mem_Tw
-- name    : Formalism.DivisionValues.ReductionFirst.cO_mem_Tw
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:18:54.870369+00:00
-- url     : https://prove2.me/theorems/71e09935-6569-4217-af33-3ad00b77c013
-- title:
--   Reduction First: c O mem Tw
-- statement:
--   The Reduction First construction uses the c O mem Tw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionLemmaFirst.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionLemmaFirst.lean#L36-L37

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

theorem Formalism.DivisionValues.ReductionFirst.cO_mem_Tw {w : HeightOneSpectrum (𝓞 K)} {s : 𝓞 K} (hs : s ∈ Tw w) : cO K s ∈ Tw w := by sorry
