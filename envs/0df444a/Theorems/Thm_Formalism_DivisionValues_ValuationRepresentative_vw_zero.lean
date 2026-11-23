-- Prove2me | Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_zero
-- name    : Formalism.DivisionValues.ValuationRepresentative.vw_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:05:01.110316+00:00
-- url     : https://prove2.me/theorems/a05de539-af9e-4e2c-8389-7b2a90a70e02
-- title:
--   Valuation Representative: vw zero
-- statement:
--   The Valuation Representative construction uses the vw zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ValBasic.lean#L62-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ValBasic.lean#L62-L63

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

theorem Formalism.DivisionValues.ValuationRepresentative.vw_zero (w : HeightOneSpectrum (𝓞 K)) : vw w (0 : K) = 0 := by sorry
