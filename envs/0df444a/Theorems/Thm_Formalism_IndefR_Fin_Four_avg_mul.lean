-- Prove2me | Theorems.Thm_Formalism_IndefR_Fin_Four_avg_mul
-- name    : Formalism.IndefR.Fin.Four.avg_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:19.859933+00:00
-- url     : https://prove2.me/theorems/07514cba-3572-4797-9bc4-5f3af2356f80
-- title:
--   Four: avg mul
-- statement:
--   The Four construction uses the avg mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/SmulSubMulLe.lean#L67-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/SmulSubMulLe.lean#L67-L89

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

theorem Formalism.IndefR.Fin.Four.avg_mul (k j : ℕ) (H : AddSubgroup W) [Finite (Qt k H)] [Finite (Qt (k * j) H)] (g : W → ℂ)
    (hg : IsInv k H g) : avg (k * j) H g = avg k H g := by sorry
