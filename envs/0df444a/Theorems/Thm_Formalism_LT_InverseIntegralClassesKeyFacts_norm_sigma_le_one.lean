-- Prove2me | Theorems.Thm_Formalism_LT_InverseIntegralClassesKeyFacts_norm_sigma_le_one
-- name    : Formalism.LT.InverseIntegralClassesKeyFacts.norm_sigma_le_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:38:03.234808+00:00
-- url     : https://prove2.me/theorems/fb236742-66d0-46c8-a818-d218eee7157c
-- title:
--   Inverse Integral Classes Key Facts: norm sigma le one
-- statement:
--   The Inverse Integral Classes Key Facts construction uses the norm sigma le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/NormSigmaLeOne.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/NormSigmaLeOne.lean#L32-L37

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

theorem Formalism.LT.InverseIntegralClassesKeyFacts.norm_sigma_le_one {p q : ℕ} {σ : K →+* K} (hσ : IsFrobLift p q σ) (hp1 : ‖(p : K)‖ ≤ 1)
    {a : K} (ha : ‖a‖ ≤ 1) : ‖σ a‖ ≤ 1 := by sorry
