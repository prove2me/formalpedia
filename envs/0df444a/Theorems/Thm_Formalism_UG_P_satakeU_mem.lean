-- Prove2me | Theorems.Thm_Formalism_UG_P_satakeU_mem
-- name    : Formalism.UG.P.satakeU_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:33:21.588712+00:00
-- url     : https://prove2.me/theorems/2121e2f2-c88f-476e-9081-ae80c10d0add
-- title:
--   P: satake U mem
-- statement:
--   The P construction uses the satake U mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SatakeMat.lean#L163-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SatakeMat.lean#L163-L170

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
variable {O}
variable (O)

theorem Formalism.UG.P.satakeU_mem (S : Finset (Fin n)) (c : satakePairs S → O) : satakeU O S c ∈ GLint (Fin n) O := by sorry
