-- Prove2me | Theorems.Thm_Formalism_IndefR_Fin_Four_QY_out
-- name    : Formalism.IndefR.Fin.Four.QY_out
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:05.336103+00:00
-- url     : https://prove2.me/theorems/1d98ac0d-f431-4f8d-8dcb-6d69cbb737a6
-- title:
--   Four: QY out
-- statement:
--   The Four construction uses the QY out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourModel.lean#L80-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourModel.lean#L80-L84

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulSubMulLe
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourModel
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
variable {L X Y : AddSubgroup W}

theorem Formalism.IndefR.Fin.Four.QY_out (y : W) : ∃ μ ∈ L ⊓ Y, (QuotientAddGroup.mk y : QY L Y).out = y + μ := by sorry
