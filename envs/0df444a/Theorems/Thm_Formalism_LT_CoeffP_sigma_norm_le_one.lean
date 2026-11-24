-- Prove2me | Theorems.Thm_Formalism_LT_CoeffP_sigma_norm_le_one
-- name    : Formalism.LT.CoeffP.sigma_norm_le_one
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T09:50:41.388736+00:00
-- url     : https://prove2.me/theorems/5fbda463-6128-48de-bb7b-1d652df2151b
-- title:
--   Coeff P: sigma norm le one
-- statement:
--   The Coeff P construction uses the sigma norm le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/SigmaNormLeOne.lean#L17-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/SigmaNormLeOne.lean#L17-L25

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
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
open Formalism Formalism.LT Formalism.LT.CoeffP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem Formalism.LT.CoeffP.sigma_norm_le_one {p q : ℕ} {σ : K →+* K} (hp : ‖(p : K)‖ ≤ 1)
    (hσ : IsFrobLift p q σ) (a : K) (ha : ‖a‖ ≤ 1) : ‖σ a‖ ≤ 1 := by sorry
