-- Prove2me | Theorems.Thm_Formalism_IndefR_Fin_Four_mem_smulSub
-- name    : Formalism.IndefR.Fin.Four.mem_smulSub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:41.752487+00:00
-- url     : https://prove2.me/theorems/825da6d7-8647-4c14-ac86-3bf5455c5214
-- title:
--   Four: mem smul Sub
-- statement:
--   The Four construction uses the mem smul Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/SmulSubMulLe.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/SmulSubMulLe.lean#L16-L17

import Mathlib
import Definitions.Def_Lemmata_MiscLemmasC_Imports
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulSubMulLe
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
open Finset
open Formalism Formalism.IndefR Formalism.IndefR.Fin Formalism.IndefR.Fin.Four
variable {W : Type*} [AddCommGroup W]

theorem Formalism.IndefR.Fin.Four.mem_smulSub {k : ℕ} {H : AddSubgroup W} {x : W} : x ∈ smulSub k H ↔ ∃ u ∈ H, k • u = x := by sorry
