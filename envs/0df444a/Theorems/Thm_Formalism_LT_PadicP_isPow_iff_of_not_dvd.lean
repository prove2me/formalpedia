-- Prove2me | Theorems.Thm_Formalism_LT_PadicP_isPow_iff_of_not_dvd
-- name    : Formalism.LT.PadicP.isPow_iff_of_not_dvd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:13:34.068333+00:00
-- url     : https://prove2.me/theorems/7d142f4e-2aa6-4917-84e0-c60ffde48c45
-- title:
--   Padic P: is Pow iff of not dvd
-- statement:
--   The Padic P construction uses the is Pow iff of not dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/IsHomOfSubstEqSmul.lean#L97-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/IsHomOfSubstEqSmul.lean#L97-L104

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

theorem Formalism.LT.PadicP.isPow_iff_of_not_dvd (n : ℕ) (h : ¬ p ∣ n) : (∃ k : ℕ, p ^ k = n) ↔ n = 1 := by sorry
