-- Prove2me | Theorems.Thm_Formalism_IndefR_Fin_Four_IsInv_cmul
-- name    : Formalism.IndefR.Fin.Four.IsInv.cmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:04.725112+00:00
-- url     : https://prove2.me/theorems/83b74b63-3c59-4474-b26a-f0faea450292
-- title:
--   Is Inv: cmul
-- statement:
--   The Is Inv construction uses the cmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/SmulSubMulLe.lean#L141-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/SmulSubMulLe.lean#L141-L143

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
omit hfin

theorem Formalism.IndefR.Fin.Four.IsInv.cmul {k : ℕ} {g : W → ℂ} (hg : IsInv k H g) (c : ℂ) : IsInv k H (fun t => c * g t) := by sorry
