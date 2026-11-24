-- Prove2me | Theorems.Thm_Formalism_UG_P_satakeInv_insert_not_mem
-- name    : Formalism.UG.P.satakeInv_insert_not_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:32:49.417349+00:00
-- url     : https://prove2.me/theorems/d4d103f1-1d7f-4aef-9eb6-d7b9affabd54
-- title:
--   P: satake Inv insert not mem
-- statement:
--   The P construction uses the satake Inv insert not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SatakeComb.lean#L10-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SatakeComb.lean#L10-L25

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.UG Formalism.UG.P
open Finset

theorem Formalism.UG.P.satakeInv_insert_not_mem {α : Type} [LinearOrder α] (s' S : Finset α) (m : α)
    (hm : ∀ x ∈ s', x < m) (hS : S ⊆ s') :
    satakeInv (insert m s') S = satakeInv s' S + S.card := by sorry
