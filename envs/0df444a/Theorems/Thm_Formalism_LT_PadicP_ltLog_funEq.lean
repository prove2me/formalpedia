-- Prove2me | Theorems.Thm_Formalism_LT_PadicP_ltLog_funEq
-- name    : Formalism.LT.PadicP.ltLog_funEq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:39:19.203805+00:00
-- url     : https://prove2.me/theorems/876cded1-36b8-42bf-8ea6-efdcd82531a7
-- title:
--   Padic P: lt Log fun Eq
-- statement:
--   The Padic P construction uses the lt Log fun Eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/IsHomOfSubstEqSmul.lean#L131-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/IsHomOfSubstEqSmul.lean#L131-L151

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

theorem Formalism.LT.PadicP.ltLog_funEq :
    ltLog p - (p : ℚ_[p])⁻¹ • (ltLog p).subst ((X : PowerSeries ℚ_[p]) ^ p) = X := by sorry
