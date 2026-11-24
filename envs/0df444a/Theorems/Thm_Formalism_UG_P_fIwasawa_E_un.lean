-- Prove2me | Theorems.Thm_Formalism_UG_P_fIwasawa_E_un
-- name    : Formalism.UG.P.fIwasawa_E_un
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:31:32.209797+00:00
-- url     : https://prove2.me/theorems/fb6ed749-f293-48ed-a699-634b4e16c801
-- title:
--   P: f Iwasawa E un
-- statement:
--   The P construction uses the f Iwasawa E un property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FIwasawaB.lean#L44-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FIwasawaB.lean#L44-L75

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

theorem Formalism.UG.P.fIwasawa_E_un (hσ : ∀ x, σ (σ x) = x) (e z : Fin n → L) (c : L)
    (hee : fIwasawaH σ e e = 0) (hez : fIwasawaH σ e z = 0)
    (hc : c + σ c + fIwasawaH σ z z = 0) : fIwasawaUn σ (fIwasawaE σ e z c) := by sorry
