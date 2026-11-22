-- Prove2me | Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_conjPl_conjPl
-- name    : Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T17:53:24.336407+00:00
-- url     : https://prove2.me/theorems/a6ef5951-a8ba-46aa-98de-9ffe5c8207a7
-- title:
--   Valuation Representative: conj Pl conj Pl
-- statement:
--   The Valuation Representative construction uses the conj Pl conj Pl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ValBasic.lean#L30-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ValBasic.lean#L30-L30

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

theorem Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl (w : HeightOneSpectrum (𝓞 K)) : conjPl (conjPl w) = w := by sorry
