-- Prove2me | Theorems.Thm_Formalism_LT_InverseIntegralClassesKeyFacts_norm_sub_le_of
-- name    : Formalism.LT.InverseIntegralClassesKeyFacts.norm_sub_le_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:57:17.257988+00:00
-- url     : https://prove2.me/theorems/f8526fa7-6bbe-4267-9d09-12cef69c93c7
-- title:
--   Inverse Integral Classes Key Facts: norm sub le of
-- statement:
--   The Inverse Integral Classes Key Facts construction uses the norm sub le of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/NormSigmaLeOne.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/NormSigmaLeOne.lean#L29-L30

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormSigmaLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u v
open Formalism Formalism.LT
open Formalism.G
open Formalism.LT.InverseIntegralClassesKeyFacts
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem Formalism.LT.InverseIntegralClassesKeyFacts.norm_sub_le_of {a b : K} {C : ℝ} (ha : ‖a‖ ≤ C) (hb : ‖b‖ ≤ C) : ‖a - b‖ ≤ C := by sorry
