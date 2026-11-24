-- Prove2me | Theorems.Thm_Formalism_IndefR_Fin_Four_isSB_ind
-- name    : Formalism.IndefR.Fin.Four.isSB_ind
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:17.521449+00:00
-- url     : https://prove2.me/theorems/2e480aaf-b597-4273-9b26-215f3793b3fe
-- title:
--   Four: is SB ind
-- statement:
--   The Four construction uses the is SB ind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourExist.lean#L102-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourExist.lean#L102-L111

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
open Classical

theorem Formalism.IndefR.Fin.Four.isSB_ind : IsSB L X (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) := by sorry
