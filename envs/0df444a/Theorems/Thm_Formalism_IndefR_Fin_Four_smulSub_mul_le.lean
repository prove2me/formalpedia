-- Prove2me | Theorems.Thm_Formalism_IndefR_Fin_Four_smulSub_mul_le
-- name    : Formalism.IndefR.Fin.Four.smulSub_mul_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:05.658556+00:00
-- url     : https://prove2.me/theorems/18048fb9-3ee9-4c7f-9e13-21a33a28e39c
-- title:
--   Four: smul Sub mul le
-- statement:
--   The Four construction uses the smul Sub mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/SmulSubMulLe.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/SmulSubMulLe.lean#L19-L22

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

theorem Formalism.IndefR.Fin.Four.smulSub_mul_le (k j : ℕ) (H : AddSubgroup W) : smulSub (k * j) H ≤ smulSub k H := by sorry
