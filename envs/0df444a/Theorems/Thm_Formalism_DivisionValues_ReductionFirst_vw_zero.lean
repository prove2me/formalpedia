-- Prove2me | Theorems.Thm_Formalism_DivisionValues_ReductionFirst_vw_zero
-- name    : Formalism.DivisionValues.ReductionFirst.vw_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:28.895915+00:00
-- url     : https://prove2.me/theorems/a228b505-1e18-4d6d-9db5-4bcb08f8c8c6
-- title:
--   Reduction First: vw zero
-- statement:
--   The Reduction First construction uses the vw zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionLemmaFirst.lean#L71-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionLemmaFirst.lean#L71-L72

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

theorem Formalism.DivisionValues.ReductionFirst.vw_zero (w : HeightOneSpectrum (𝓞 K)) : vw w (0 : K) = 0 := by sorry
