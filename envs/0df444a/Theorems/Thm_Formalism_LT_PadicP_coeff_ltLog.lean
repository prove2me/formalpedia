-- Prove2me | Theorems.Thm_Formalism_LT_PadicP_coeff_ltLog
-- name    : Formalism.LT.PadicP.coeff_ltLog
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:57:17.63471+00:00
-- url     : https://prove2.me/theorems/e9b68315-797a-4870-9d28-fd7c4ada16ca
-- title:
--   Padic P: coeff lt Log
-- statement:
--   The Padic P construction uses the coeff lt Log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/IsHomOfSubstEqSmul.lean#L79-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/IsHomOfSubstEqSmul.lean#L79-L82

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
open Classical

theorem Formalism.LT.PadicP.coeff_ltLog (n : ℕ) :
    coeff n (ltLog p) = if ∃ k : ℕ, p ^ k = n then ((n : ℚ_[p]))⁻¹ else 0 := by sorry
