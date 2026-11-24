-- Prove2me | Theorems.Thm_Formalism_IndefR_Fin_Four_IsSB_add
-- name    : Formalism.IndefR.Fin.Four.IsSB.add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:05.722288+00:00
-- url     : https://prove2.me/theorems/83d4bd85-0b0c-4b02-9fbc-d4c2a8433c88
-- title:
--   Is SB: add
-- statement:
--   The Is SB construction uses the add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourExist.lean#L18-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourExist.lean#L18-L37

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourModel
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourExist
import Theorems.Thm_Formalism_IndefR_Fin_Four_IsInv_add

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

theorem Formalism.IndefR.Fin.Four.IsSB.add {Φ Φ' : W → ℂ} (h : IsSB L X Φ) (h' : IsSB L X Φ') : IsSB L X (Φ + Φ') := by sorry
