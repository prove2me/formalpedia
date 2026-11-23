-- Prove2me | Theorems.Thm_Formalism_DivisionValues_meanLog_mul
-- name    : Formalism.DivisionValues.meanLog_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:05.967832+00:00
-- url     : https://prove2.me/theorems/6f2ea528-70a5-46ce-8ecb-e79557b60a9a
-- title:
--   Division Values: mean Log mul
-- statement:
--   The Division Values construction uses the mean Log mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/KappaNormalise.lean#L251-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/KappaNormalise.lean#L251-L256

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

theorem Formalism.DivisionValues.meanLog_mul (t κ : InfinitePlace K → ℝ) (ht : ∀ v, 0 < t v) (hκ : ∀ v, 0 < κ v) :
    meanLog (fun v => t v * κ v) = meanLog t + meanLog κ := by sorry
