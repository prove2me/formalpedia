-- Prove2me | Theorems.Thm_Formalism_DivisionValues_ReductionFirst_vw_int_nonneg
-- name    : Formalism.DivisionValues.ReductionFirst.vw_int_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:02:17.643888+00:00
-- url     : https://prove2.me/theorems/76826685-98f8-49d1-97e7-9dceec63bd10
-- title:
--   Reduction First: vw int nonneg
-- statement:
--   The Reduction First construction uses the vw int nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionLemmaFirst.lean#L89-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionLemmaFirst.lean#L89-L92

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

theorem Formalism.DivisionValues.ReductionFirst.vw_int_nonneg (w : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) : 0 ≤ vw w (r : K) := by sorry
