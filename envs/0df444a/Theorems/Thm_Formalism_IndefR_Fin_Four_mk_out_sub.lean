-- Prove2me | Theorems.Thm_Formalism_IndefR_Fin_Four_mk_out_sub
-- name    : Formalism.IndefR.Fin.Four.mk_out_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:10:23.828504+00:00
-- url     : https://prove2.me/theorems/02d40075-408f-4925-8ef3-dc42e990dfdc
-- title:
--   Four: mk out sub
-- statement:
--   The Four construction uses the mk out sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourUniq.lean#L31-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourUniq.lean#L31-L37

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulFinsum
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourUniq
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

theorem Formalism.IndefR.Fin.Four.mk_out_sub (S : AddSubgroup W) (a : W) : ∃ l ∈ S, (QuotientAddGroup.mk a : W ⧸ S).out = a + l := by sorry
