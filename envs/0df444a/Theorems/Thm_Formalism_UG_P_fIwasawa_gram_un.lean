-- Prove2me | Theorems.Thm_Formalism_UG_P_fIwasawa_gram_un
-- name    : Formalism.UG.P.fIwasawa_gram_un
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:59:54.604563+00:00
-- url     : https://prove2.me/theorems/eb4ed3a4-a1dc-478e-966b-efeabe5779f4
-- title:
--   P: f Iwasawa gram un
-- statement:
--   The P construction uses the f Iwasawa gram un property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FIwasawaC.lean#L136-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FIwasawaC.lean#L136-L154

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaC
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

theorem Formalism.UG.P.fIwasawa_gram_un (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) (a b : Fin n) :
    ∑ j, σ (M (Fin.rev j) a) * M j b = if b = Fin.rev a then 1 else 0 := by sorry
