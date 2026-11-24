-- Prove2me | Theorems.Thm_Formalism_UG_P_satakeInv_insert_mem
-- name    : Formalism.UG.P.satakeInv_insert_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:33:07.556272+00:00
-- url     : https://prove2.me/theorems/a3efbaef-af9f-4d52-8b0b-e30d7d664c86
-- title:
--   P: satake Inv insert mem
-- statement:
--   The P construction uses the satake Inv insert mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SatakeComb.lean#L27-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SatakeComb.lean#L27-L44

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

theorem Formalism.UG.P.satakeInv_insert_mem {α : Type} [LinearOrder α] (s' T : Finset α) (m : α)
    (hm : ∀ x ∈ s', x < m) (hT : T ⊆ s') :
    satakeInv (insert m s') (insert m T) = satakeInv s' T := by sorry
