-- Prove2me | Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_lw_conjPl
-- name    : Formalism.DivisionValues.ValuationRepresentative.lw_conjPl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:20:00.698139+00:00
-- url     : https://prove2.me/theorems/38810f9f-4556-468f-a097-884b5cf7c203
-- title:
--   Valuation Representative: lw conj Pl
-- statement:
--   The Valuation Representative construction uses the lw conj Pl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ValBasic.lean#L128-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ValBasic.lean#L128-L130

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

theorem Formalism.DivisionValues.ValuationRepresentative.lw_conjPl (w : HeightOneSpectrum (𝓞 K)) : lw (conjPl w) = lw w := by sorry
