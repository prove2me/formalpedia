-- Prove2me | Theorems.Thm_Formalism_IndefR_Fin_Four_IsInv_mul
-- name    : Formalism.IndefR.Fin.Four.IsInv.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:06.592811+00:00
-- url     : https://prove2.me/theorems/327a957a-8199-49ee-98b4-0d518d9b9e5c
-- title:
--   Is Inv: mul
-- statement:
--   The Is Inv construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/SmulSubMulLe.lean#L53-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/SmulSubMulLe.lean#L53-L56

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

theorem Formalism.IndefR.Fin.Four.IsInv.mul {k : ℕ} {H : AddSubgroup W} {g : W → ℂ} (hg : IsInv k H g) (j : ℕ) : IsInv (k * j) H g := by sorry
