-- Prove2me | Theorems.Thm_Formalism_UG_P_satakeN_mem
-- name    : Formalism.UG.P.satakeN_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:32:57.214852+00:00
-- url     : https://prove2.me/theorems/fc52e51a-b182-4284-8638-eee5fe3c5ed3
-- title:
--   P: satake N mem
-- statement:
--   The P construction uses the satake N mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SatakeMat.lean#L44-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SatakeMat.lean#L44-L49

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

theorem Formalism.UG.P.satakeN_mem (S : Finset (Fin n)) (c : satakePairs S → O) (a l : Fin n) :
    satakeN O S c a l ∈ O := by sorry
