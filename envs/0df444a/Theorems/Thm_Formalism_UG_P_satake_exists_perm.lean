-- Prove2me | Theorems.Thm_Formalism_UG_P_satake_exists_perm
-- name    : Formalism.UG.P.satake_exists_perm
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:32:54.189419+00:00
-- url     : https://prove2.me/theorems/7d391ec5-69e4-446c-a132-9e0c59db1717
-- title:
--   P: satake exists perm
-- statement:
--   The P construction uses the satake exists perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SatakeMat.lean#L193-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SatakeMat.lean#L193-L200

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

theorem Formalism.UG.P.satake_exists_perm (S : Finset (Fin n)) :
    ∃ σ : Equiv.Perm (Fin n), ∀ a, a ∈ S ↔ ((σ a : Fin n) : ℕ) < S.card := by sorry
