-- Prove2me | Theorems.Thm_Formalism_IndefR_Fin_Four_IsInv_shift
-- name    : Formalism.IndefR.Fin.Four.IsInv.shift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:09.90963+00:00
-- url     : https://prove2.me/theorems/141416bc-e816-42e6-9789-074bb0801902
-- title:
--   Is Inv: shift
-- statement:
--   The Is Inv construction uses the shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/SmulSubMulLe.lean#L155-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/SmulSubMulLe.lean#L155-L159

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

theorem Formalism.IndefR.Fin.Four.IsInv.shift {k : ℕ} {g : W → ℂ} (hg : IsInv k H g) {v : W} (hv : v ∈ H) :
    IsInv k H (fun t => g (t + v)) := by sorry
