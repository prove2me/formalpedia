-- Prove2me | Theorems.Thm_Formalism_DivisionValues_mean_log_sqrt_inv
-- name    : Formalism.DivisionValues.mean_log_sqrt_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:15.000375+00:00
-- url     : https://prove2.me/theorems/5cc69d93-9f42-413b-a4ca-ab4b02d19992
-- title:
--   Division Values: mean log sqrt inv
-- statement:
--   The Division Values construction uses the mean log sqrt inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/KappaNormalise.lean#L225-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/KappaNormalise.lean#L225-L232

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_PassageScaleFree
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_KappaNormalise
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
variable {K : Type} [Field K] [NumberField K]

theorem Formalism.DivisionValues.mean_log_sqrt_inv (t : InfinitePlace K → ℝ) (ht : ∀ v, 0 < t v) :
    2 * ((1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Real.sqrt (t v))⁻¹) = -meanLog t := by sorry
