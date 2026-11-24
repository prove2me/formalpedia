-- Prove2me | Theorems.Thm_Formalism_IndefR_Fin_Four_out_mk
-- name    : Formalism.IndefR.Fin.Four.out_mk
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:25.436819+00:00
-- url     : https://prove2.me/theorems/485a822c-a6e3-47d3-8a0d-49f4d73f3b99
-- title:
--   Four: out mk
-- statement:
--   The Four construction uses the out mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/SmulSubMulLe.lean#L31-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/SmulSubMulLe.lean#L31-L39

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

theorem Formalism.IndefR.Fin.Four.out_mk (k : ℕ) (H : AddSubgroup W) (x : H) :
    ∃ u ∈ H, ((((QuotientAddGroup.mk x : Qt k H)).out : H) : W) + k • u = (x : W) := by sorry
