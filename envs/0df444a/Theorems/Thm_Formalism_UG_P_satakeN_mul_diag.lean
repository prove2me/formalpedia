-- Prove2me | Theorems.Thm_Formalism_UG_P_satakeN_mul_diag
-- name    : Formalism.UG.P.satakeN_mul_diag
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:33:04.114752+00:00
-- url     : https://prove2.me/theorems/29f1c2bf-7317-4160-b08a-0b7fa8c81200
-- title:
--   P: satake N mul diag
-- statement:
--   The P construction uses the satake N mul diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SatakeMat.lean#L60-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SatakeMat.lean#L60-L66

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

theorem Formalism.UG.P.satakeN_mul_diag (S S' : Finset (Fin n)) (c : satakePairs S → O) (c' : satakePairs S' → O)
    (a : Fin n) : (satakeN O S c * satakeN O S' c') a a = 0 := by sorry
