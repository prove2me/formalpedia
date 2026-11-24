-- Prove2me | Theorems.Thm_Formalism_LT_PadicP_isPow_mul_iff
-- name    : Formalism.LT.PadicP.isPow_mul_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:13:34.007808+00:00
-- url     : https://prove2.me/theorems/74dcb76d-7832-4856-9e25-52b0b663867f
-- title:
--   Padic P: is Pow mul iff
-- statement:
--   The Padic P construction uses the is Pow mul iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/IsHomOfSubstEqSmul.lean#L84-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/IsHomOfSubstEqSmul.lean#L84-L95

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

theorem Formalism.LT.PadicP.isPow_mul_iff (m : ℕ) : (∃ k : ℕ, p ^ k = p * m) ↔ ∃ k : ℕ, p ^ k = m := by sorry
