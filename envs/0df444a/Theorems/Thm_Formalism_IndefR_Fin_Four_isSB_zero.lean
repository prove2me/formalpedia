-- Prove2me | Theorems.Thm_Formalism_IndefR_Fin_Four_isSB_zero
-- name    : Formalism.IndefR.Fin.Four.isSB_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:37.826969+00:00
-- url     : https://prove2.me/theorems/0116c274-4b7b-4e89-a9b3-19920e5f8879
-- title:
--   Four: is SB zero
-- statement:
--   The Four construction uses the is SB zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourExist.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourExist.lean#L15-L16

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourModel
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourExist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.Fin Formalism.IndefR.Fin.Four
variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]
variable {L X : AddSubgroup W}

theorem Formalism.IndefR.Fin.Four.isSB_zero : IsSB L X (0 : W → ℂ) := by sorry
