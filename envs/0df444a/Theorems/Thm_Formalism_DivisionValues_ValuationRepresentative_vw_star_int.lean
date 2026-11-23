-- Prove2me | Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_star_int
-- name    : Formalism.DivisionValues.ValuationRepresentative.vw_star_int
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:20:09.399825+00:00
-- url     : https://prove2.me/theorems/249baf1f-ea50-4574-87d7-7a6d96b7723e
-- title:
--   Valuation Representative: vw star int
-- statement:
--   The Valuation Representative construction uses the vw star int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ValBasic.lean#L93-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ValBasic.lean#L93-L102

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

theorem Formalism.DivisionValues.ValuationRepresentative.vw_star_int (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    vw w (star (x : K)) = vw (conjPl w) (x : K) := by sorry
