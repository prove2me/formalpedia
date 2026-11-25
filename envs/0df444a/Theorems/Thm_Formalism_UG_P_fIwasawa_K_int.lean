-- Prove2me | Theorems.Thm_Formalism_UG_P_fIwasawa_K_int
-- name    : Formalism.UG.P.fIwasawa_K_int
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:58:16.693147+00:00
-- url     : https://prove2.me/theorems/29fbaefa-14d8-5eb9-bb5f-8ef5496432c0
-- title:
--   P: f Iwasawa K int
-- statement:
--   The P construction uses the f Iwasawa K int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FIwasawaB.lean#L151-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FIwasawaB.lean#L151-L158

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

theorem Formalism.UG.P.fIwasawa_K_int (k : GU σ n) (hk : k ∈ KU σ n) :
    fIwasawaInt (((k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) := by sorry
