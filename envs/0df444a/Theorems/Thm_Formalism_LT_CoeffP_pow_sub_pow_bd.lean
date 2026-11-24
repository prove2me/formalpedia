-- Prove2me | Theorems.Thm_Formalism_LT_CoeffP_pow_sub_pow_bd
-- name    : Formalism.LT.CoeffP.pow_sub_pow_bd
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T09:51:35.324981+00:00
-- url     : https://prove2.me/theorems/8752ff55-e898-4a4c-8da0-5d8afaa47983
-- title:
--   Coeff P: pow sub pow bd
-- statement:
--   The Coeff P construction uses the pow sub pow bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/SigmaNormLeOne.lean#L201-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/SigmaNormLeOne.lean#L201-L213

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
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type v}

theorem Formalism.LT.CoeffP.pow_sub_pow_bd {c : ℝ} (hc : 0 ≤ c) {A B : MvPowerSeries ι K} (hA : Bd 1 A) (hB : Bd 1 B)
    (hD : Bd c (A - B)) (m : ℕ) : Bd c (A ^ m - B ^ m) := by sorry
