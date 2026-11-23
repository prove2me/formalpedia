-- Prove2me | Theorems.Thm_Formalism_DivisionValues_ValuationZeroReduction_vw_eq_zero_of_not_mem
-- name    : Formalism.DivisionValues.ValuationZeroReduction.vw_eq_zero_of_not_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:20:08.114735+00:00
-- url     : https://prove2.me/theorems/456b0578-0293-474c-9385-1738d38a076b
-- title:
--   Valuation Zero Reduction: vw eq zero of not mem
-- statement:
--   The Valuation Zero Reduction construction uses the vw eq zero of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/VwEqZeroOfNotMem.lean#L16-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/VwEqZeroOfNotMem.lean#L16-L30

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_StatementACE
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_VwEqZeroOfNotMem
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
open Formalism.DivisionValues.ValuationZeroReduction
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.DivisionValues.ValuationZeroReduction.vw_eq_zero_of_not_mem (w : HeightOneSpectrum (𝓞 K)) (s : 𝓞 K) (hs : s ∉ w.asIdeal) :
    vw w (s : K) = 0 := by sorry
