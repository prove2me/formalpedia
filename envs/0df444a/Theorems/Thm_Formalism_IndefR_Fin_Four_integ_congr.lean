-- Prove2me | Theorems.Thm_Formalism_IndefR_Fin_Four_integ_congr
-- name    : Formalism.IndefR.Fin.Four.integ_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:40.654186+00:00
-- url     : https://prove2.me/theorems/317ba2aa-f888-4697-bc66-0792668a0590
-- title:
--   Four: integ congr
-- statement:
--   The Four construction uses the integ congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/SmulSubMulLe.lean#L122-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/SmulSubMulLe.lean#L122-L129

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
variable {H : AddSubgroup W} (hfin : ∀ k, 0 < k → Finite (Qt k H))
include hfin

theorem Formalism.IndefR.Fin.Four.integ_congr {g g' : W → ℂ} (h : ∀ t ∈ H, g t = g' t) : integ H g = integ H g' := by sorry
