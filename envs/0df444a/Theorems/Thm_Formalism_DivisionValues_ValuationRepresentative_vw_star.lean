-- Prove2me | Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_star
-- name    : Formalism.DivisionValues.ValuationRepresentative.vw_star
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T17:53:11.895445+00:00
-- url     : https://prove2.me/theorems/7ffd58f7-d034-4609-86ea-e87d9f2f4b66
-- title:
--   Valuation Representative: vw star
-- statement:
--   The Valuation Representative construction uses the vw star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ValBasic.lean#L108-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ValBasic.lean#L108-L119

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

theorem Formalism.DivisionValues.ValuationRepresentative.vw_star (w : HeightOneSpectrum (𝓞 K)) (a : K) :
    vw w (star a) = vw (conjPl w) a := by sorry
