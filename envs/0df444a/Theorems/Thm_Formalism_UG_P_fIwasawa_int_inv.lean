-- Prove2me | Theorems.Thm_Formalism_UG_P_fIwasawa_int_inv
-- name    : Formalism.UG.P.fIwasawa_int_inv
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:31:40.929793+00:00
-- url     : https://prove2.me/theorems/c2df80fb-5d29-4ac4-92e6-fffe12af0db9
-- title:
--   P: f Iwasawa int inv
-- statement:
--   The P construction uses the f Iwasawa int inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FIwasawaB.lean#L96-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FIwasawaB.lean#L96-L108

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
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) {n : ℕ}

theorem Formalism.UG.P.fIwasawa_int_inv (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (M : Matrix (Fin n) (Fin n) L)
    (hM : fIwasawaInt M) : fIwasawaInt (fIwasawaInv σ M) := by sorry
