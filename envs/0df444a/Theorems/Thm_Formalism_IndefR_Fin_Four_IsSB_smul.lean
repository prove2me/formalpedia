-- Prove2me | Theorems.Thm_Formalism_IndefR_Fin_Four_IsSB_smul
-- name    : Formalism.IndefR.Fin.Four.IsSB.smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:35.764626+00:00
-- url     : https://prove2.me/theorems/ea116bb1-11be-4fbc-838d-d1de03e59e49
-- title:
--   Is SB: smul
-- statement:
--   The Is SB construction uses the smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourExist.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourExist.lean#L39-L43

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

theorem Formalism.IndefR.Fin.Four.IsSB.smul {Φ : W → ℂ} (h : IsSB L X Φ) (c : ℂ) : IsSB L X (c • Φ) := by sorry
