-- Prove2me | Theorems.Thm_Formalism_IndefR_Fin_Four_QX_out
-- name    : Formalism.IndefR.Fin.Four.QX_out
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:07.595743+00:00
-- url     : https://prove2.me/theorems/4dc2c69c-2d9e-4a8c-a6a0-0bd5facba05a
-- title:
--   Four: QX out
-- statement:
--   The Four construction uses the QX out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourModel.lean#L74-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourModel.lean#L74-L78

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

theorem Formalism.IndefR.Fin.Four.QX_out (a : W) : ∃ l ∈ L ⊓ X, (QuotientAddGroup.mk a : QX L X).out = a + l := by sorry
