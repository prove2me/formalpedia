-- Prove2me | Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_cO_apply
-- name    : Formalism.DivisionValues.ValuationRepresentative.cO_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:04:50.597792+00:00
-- url     : https://prove2.me/theorems/fe98727c-7806-48de-bd25-2dd650f8dce6
-- title:
--   Valuation Representative: c O apply
-- statement:
--   The Valuation Representative construction uses the c O apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ValBasic.lean#L15-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ValBasic.lean#L15-L15

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.ValuationRepresentative
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.DivisionValues.ValuationRepresentative.cO_apply (x : 𝓞 K) : ((cO K x : 𝓞 K) : K) = star (x : K) := by sorry
