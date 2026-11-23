-- Prove2me | Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_map_cO_le_iff
-- name    : Formalism.DivisionValues.ValuationRepresentative.map_cO_le_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:20:11.808234+00:00
-- url     : https://prove2.me/theorems/8655d551-ffee-4a9c-bd7b-164b23857e58
-- title:
--   Valuation Representative: map c O le iff
-- statement:
--   The Valuation Representative construction uses the map c O le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ValBasic.lean#L32-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ValBasic.lean#L32-L38

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

theorem Formalism.DivisionValues.ValuationRepresentative.map_cO_le_iff (I J : Ideal (𝓞 K)) : I.map (cO K) ≤ J.map (cO K) ↔ I ≤ J := by sorry
