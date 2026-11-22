-- Prove2me | Theorems.Thm_Formalism_UG_P_fIwasawa_E_mulVec
-- name    : Formalism.UG.P.fIwasawa_E_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:42:13.176439+00:00
-- url     : https://prove2.me/theorems/2de602ae-f0b8-4dcc-ab92-9827281c8cdc
-- title:
--   P: f Iwasawa E mul Vec
-- statement:
--   The P construction uses the f Iwasawa E mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FIwasawaB.lean#L34-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FIwasawaB.lean#L34-L42

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaA
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaB
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

theorem Formalism.UG.P.fIwasawa_E_mulVec (e z : Fin n → L) (c : L) (w : Fin n → L) :
    fIwasawaE σ e z c *ᵥ w = w + fIwasawaH σ e w • z - fIwasawaH σ z w • e +
      (c * fIwasawaH σ e w) • e := by sorry
