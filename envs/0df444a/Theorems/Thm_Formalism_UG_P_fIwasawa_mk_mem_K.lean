-- Prove2me | Theorems.Thm_Formalism_UG_P_fIwasawa_mk_mem_K
-- name    : Formalism.UG.P.fIwasawa_mk_mem_K
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:38.480808+00:00
-- url     : https://prove2.me/theorems/1a851d02-e90a-4cc1-af0a-985d1b73f55c
-- title:
--   P: f Iwasawa mk mem K
-- statement:
--   The P construction uses the f Iwasawa mk mem K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FIwasawaB.lean#L129-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FIwasawaB.lean#L129-L149

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

theorem Formalism.UG.P.fIwasawa_mk_mem_K (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (M : Matrix (Fin n) (Fin n) L)
    (hM : fIwasawaUn σ M) (hI : fIwasawaInt M) : fIwasawaMk σ M hM ∈ KU σ n := by sorry
