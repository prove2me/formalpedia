-- Prove2me | Theorems.Thm_Formalism_IndefR_Fin_Four_avg_eq_sum
-- name    : Formalism.IndefR.Fin.Four.avg_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:51.896576+00:00
-- url     : https://prove2.me/theorems/324eb559-6130-4882-a64c-159c8b9d7054
-- title:
--   Four: avg eq sum
-- statement:
--   The Four construction uses the avg eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/SmulSubMulLe.lean#L58-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/SmulSubMulLe.lean#L58-L60

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

theorem Formalism.IndefR.Fin.Four.avg_eq_sum (k : ℕ) (H : AddSubgroup W) [Fintype (Qt k H)] (g : W → ℂ) :
    avg k H g = (Fintype.card (Qt k H) : ℂ)⁻¹ * ∑ q : Qt k H, g ((q.out : H) : W) := by sorry
