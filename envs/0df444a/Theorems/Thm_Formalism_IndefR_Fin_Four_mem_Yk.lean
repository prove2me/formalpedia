-- Prove2me | Theorems.Thm_Formalism_IndefR_Fin_Four_mem_Yk
-- name    : Formalism.IndefR.Fin.Four.mem_Yk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:33.938792+00:00
-- url     : https://prove2.me/theorems/431ad91b-9caa-43c7-a84b-2b60f73dffcf
-- title:
--   Four: mem Yk
-- statement:
--   The Four construction uses the mem Yk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourVac.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourVac.lean#L13-L14

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

theorem Formalism.IndefR.Fin.Four.mem_Yk {L Y : AddSubgroup W} {k : ℕ} {y : W} : y ∈ Yk L Y k ↔ y ∈ Y ∧ k • y ∈ L := by sorry
