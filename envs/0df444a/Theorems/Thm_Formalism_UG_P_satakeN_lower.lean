-- Prove2me | Theorems.Thm_Formalism_UG_P_satakeN_lower
-- name    : Formalism.UG.P.satakeN_lower
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:33:29.147561+00:00
-- url     : https://prove2.me/theorems/b379ea4a-746d-42d8-9fd5-b0cdfd1adc91
-- title:
--   P: satake N lower
-- statement:
--   The P construction uses the satake N lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SatakeMat.lean#L72-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SatakeMat.lean#L72-L74

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {L : Type} [Field L] (O : Subring L) {n : ℕ}

theorem Formalism.UG.P.satakeN_lower (S : Finset (Fin n)) (c : satakePairs S → O) (a l : Fin n) (h : l < a) :
    satakeN O S c a l = 0 := by sorry
