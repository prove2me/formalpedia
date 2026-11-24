-- Prove2me | Theorems.Thm_Formalism_LT_CoeffP_powp_step
-- name    : Formalism.LT.CoeffP.powp_step
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T09:51:20.773784+00:00
-- url     : https://prove2.me/theorems/20b2d6a0-ba72-43bc-9a63-55d6bcd8f004
-- title:
--   Coeff P: powp step
-- statement:
--   The Coeff P construction uses the powp step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/SigmaNormLeOne.lean#L147-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/SigmaNormLeOne.lean#L147-L190

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

theorem Formalism.LT.CoeffP.powp_step {p : ℕ} (hp : p.Prime) {r : ℕ} (hr : 1 ≤ r) {A B : MvPowerSeries ι K}
    (_hA : Bd 1 A) (hB : Bd 1 B) (hD : Bd (‖(p : K)‖ ^ r) (A - B)) :
    Bd (‖(p : K)‖ ^ (r + 1)) (A ^ p - B ^ p) := by sorry
