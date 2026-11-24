-- Prove2me | Theorems.Thm_Formalism_IndefR_Fin_Four_IsInv_mk_eq
-- name    : Formalism.IndefR.Fin.Four.IsInv.mk_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:05.903802+00:00
-- url     : https://prove2.me/theorems/0258c0d1-660e-4c2d-b90c-846dbd32e38a
-- title:
--   Is Inv: mk eq
-- statement:
--   The Is Inv construction uses the mk eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/SmulSubMulLe.lean#L41-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/SmulSubMulLe.lean#L41-L47

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

theorem Formalism.IndefR.Fin.Four.IsInv.mk_eq {k : ℕ} {H : AddSubgroup W} {g : W → ℂ} (hg : IsInv k H g) {x y : H}
    (hxy : (QuotientAddGroup.mk x : Qt k H) = QuotientAddGroup.mk y) : g x = g y := by sorry
