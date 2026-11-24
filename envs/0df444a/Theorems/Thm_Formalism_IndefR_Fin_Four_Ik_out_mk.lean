-- Prove2me | Theorems.Thm_Formalism_IndefR_Fin_Four_Ik_out_mk
-- name    : Formalism.IndefR.Fin.Four.Ik_out_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:09.318079+00:00
-- url     : https://prove2.me/theorems/9d25bdb5-4d5e-45c7-9435-29083c89ed07
-- title:
--   Four: Ik out mk
-- statement:
--   The Four construction uses the Ik out mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourVac.lean#L52-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourVac.lean#L52-L60

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourUniq
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourVac
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

theorem Formalism.IndefR.Fin.Four.Ik_out_mk {L Y : AddSubgroup W} {k : ℕ} (z : Yk L Y k) :
    ∃ v ∈ L ⊓ Y, ((((QuotientAddGroup.mk z : Ik L Y k)).out : ↥(Yk L Y k)) : W) + k • v = (z : W) := by sorry
