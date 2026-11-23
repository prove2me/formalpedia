-- Prove2me | Theorems.Thm_Formalism_UG_P_satakePairs_card
-- name    : Formalism.UG.P.satakePairs_card
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:14.543056+00:00
-- url     : https://prove2.me/theorems/98fc1b83-b46b-4220-abd2-0ce01c45e2f9
-- title:
--   P: satake Pairs card
-- statement:
--   The P construction uses the satake Pairs card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SatakeMat.lean#L16-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SatakeMat.lean#L16-L33

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

theorem Formalism.UG.P.satakePairs_card (S : Finset (Fin n)) :
    Fintype.card (satakePairs S) = satakeInv Finset.univ S := by sorry
