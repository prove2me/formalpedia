-- Prove2me | Theorems.Thm_Formalism_UG_P_satakeGL_apply
-- name    : Formalism.UG.P.satakeGL_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:17.195796+00:00
-- url     : https://prove2.me/theorems/831ad179-d85d-4904-9ca5-3039de993322
-- title:
--   P: satake GL apply
-- statement:
--   The P construction uses the satake GL apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SatakeMat.lean#L114-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SatakeMat.lean#L114-L118

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

theorem Formalism.UG.P.satakeGL_apply {π : L} (hπ : π ≠ 0) (S : Finset (Fin n)) (c : satakePairs S → O) (a l : Fin n) :
    ((satakeGL O hπ S c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a l =
      ((1 : Matrix (Fin n) (Fin n) L) a l + satakeN O S c a l) * (if l ∈ S then π else 1) := by sorry
