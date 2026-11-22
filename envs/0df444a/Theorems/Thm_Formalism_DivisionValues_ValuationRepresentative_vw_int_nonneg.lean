-- Prove2me | Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_int_nonneg
-- name    : Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:35:31.307891+00:00
-- url     : https://prove2.me/theorems/e4acbe28-ae43-465a-a226-96343fe41660
-- title:
--   Valuation Representative: vw int nonneg
-- statement:
--   The Valuation Representative construction uses the vw int nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ValBasic.lean#L89-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ValBasic.lean#L89-L91

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

theorem Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) : 0 ≤ vw w (x : K) := by sorry
