-- Prove2me | Theorems.Thm_Formalism_LT_PadicP_ltLog_subst_X_pow
-- name    : Formalism.LT.PadicP.ltLog_subst_X_pow
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T09:52:01.62132+00:00
-- url     : https://prove2.me/theorems/bc7ae734-c11a-411a-bb1f-8d8b3616bb4f
-- title:
--   Padic P: lt Log subst X pow
-- statement:
--   The Padic P construction uses the lt Log subst X pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/IsHomOfSubstEqSmul.lean#L153-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/IsHomOfSubstEqSmul.lean#L153-L159

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_IsHomOfSubstEqSmul
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
open Formalism Formalism.LT Formalism.LT.PadicP
open Formalism.G
variable {p : ℕ} [hp : Fact p.Prime]

theorem Formalism.LT.PadicP.ltLog_subst_X_pow :
    (ltLog p).subst ((X : PowerSeries ℚ_[p]) ^ p) = (p : ℚ_[p]) • (ltLog p - X) := by sorry
