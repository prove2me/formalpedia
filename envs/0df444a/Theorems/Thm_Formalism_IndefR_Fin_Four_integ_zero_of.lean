-- Prove2me | Theorems.Thm_Formalism_IndefR_Fin_Four_integ_zero_of
-- name    : Formalism.IndefR.Fin.Four.integ_zero_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:29.545233+00:00
-- url     : https://prove2.me/theorems/7454c33f-6cfa-4a6e-962a-7dd34667dd77
-- title:
--   Four: integ zero of
-- statement:
--   The Four construction uses the integ zero of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/SmulSubMulLe.lean#L216-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/SmulSubMulLe.lean#L216-L219

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

theorem Formalism.IndefR.Fin.Four.integ_zero_of {g : W → ℂ} (h : ∀ t ∈ H, g t = 0) : integ H g = 0 := by sorry
