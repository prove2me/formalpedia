-- Prove2me | Theorems.Thm_Formalism_UG_P_satakeInv_two_mul
-- name    : Formalism.UG.P.satakeInv_two_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:32:52.182106+00:00
-- url     : https://prove2.me/theorems/e687a142-b923-443c-a003-b698355ff11c
-- title:
--   P: satake Inv two mul
-- statement:
--   The P construction uses the satake Inv two mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SatakeComb.lean#L146-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SatakeComb.lean#L146-L164

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

theorem Formalism.UG.P.satakeInv_two_mul {n : ℕ} (S : Finset (Fin n)) :
    2 * (satakeInv univ S : ℤ) =
      ∑ a ∈ S, ((n : ℤ) - 1 - 2 * (a : ℕ)) + (S.card : ℤ) * ((n : ℤ) - S.card) := by sorry
