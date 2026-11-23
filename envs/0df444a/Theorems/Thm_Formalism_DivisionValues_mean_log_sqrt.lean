-- Prove2me | Theorems.Thm_Formalism_DivisionValues_mean_log_sqrt
-- name    : Formalism.DivisionValues.mean_log_sqrt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:16.888679+00:00
-- url     : https://prove2.me/theorems/d5fcc0d1-ba87-41c6-aea1-cd9b73a73be3
-- title:
--   Division Values: mean log sqrt
-- statement:
--   The Division Values construction uses the mean log sqrt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/KappaNormalise.lean#L216-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/KappaNormalise.lean#L216-L223

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

theorem Formalism.DivisionValues.mean_log_sqrt (t : InfinitePlace K → ℝ) (ht : ∀ v, 0 < t v) :
    2 * ((1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Real.sqrt (t v))) = meanLog t := by sorry
