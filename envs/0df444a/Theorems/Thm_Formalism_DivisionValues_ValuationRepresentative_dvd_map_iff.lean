-- Prove2me | Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_dvd_map_iff
-- name    : Formalism.DivisionValues.ValuationRepresentative.dvd_map_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:19:44.768072+00:00
-- url     : https://prove2.me/theorems/42781232-9f87-46bb-821e-a4aaf2f0edb5
-- title:
--   Valuation Representative: dvd map iff
-- statement:
--   The Valuation Representative construction uses the dvd map iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ValBasic.lean#L40-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ValBasic.lean#L40-L42

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

theorem Formalism.DivisionValues.ValuationRepresentative.dvd_map_iff (v : HeightOneSpectrum (𝓞 K)) (J : Ideal (𝓞 K)) (n : ℕ) :
    (v.asIdeal.map (cO K)) ^ n ∣ J.map (cO K) ↔ v.asIdeal ^ n ∣ J := by sorry
