-- Prove2me | Theorems.Thm_Formalism_UG_P_fIwasawa_H_single_left
-- name    : Formalism.UG.P.fIwasawa_H_single_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:24:17.70479+00:00
-- url     : https://prove2.me/theorems/3b628ebb-853e-4ceb-9f99-f14342a733c0
-- title:
--   P: f Iwasawa H single left
-- statement:
--   The P construction uses the f Iwasawa H single left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FIwasawaA.lean#L48-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FIwasawaA.lean#L48-L56

import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SphericalA
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] (σ : L →+* L) {n : ℕ}

theorem Formalism.UG.P.fIwasawa_H_single_left (p : Fin n) (w : Fin n → L) :
    fIwasawaH σ (Pi.single p 1) w = w (Fin.rev p) := by sorry
