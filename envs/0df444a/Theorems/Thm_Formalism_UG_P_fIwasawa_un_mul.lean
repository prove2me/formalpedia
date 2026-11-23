-- Prove2me | Theorems.Thm_Formalism_UG_P_fIwasawa_un_mul
-- name    : Formalism.UG.P.fIwasawa_un_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:24:10.90561+00:00
-- url     : https://prove2.me/theorems/88bfe7f3-2104-465f-bdcc-b891a48e173d
-- title:
--   P: f Iwasawa un mul
-- statement:
--   The P construction uses the f Iwasawa un mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FIwasawaA.lean#L69-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FIwasawaA.lean#L69-L73

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

theorem Formalism.UG.P.fIwasawa_un_mul (A B : Matrix (Fin n) (Fin n) L) (hA : fIwasawaUn σ A) (hB : fIwasawaUn σ B) :
    fIwasawaUn σ (A * B) := by sorry
