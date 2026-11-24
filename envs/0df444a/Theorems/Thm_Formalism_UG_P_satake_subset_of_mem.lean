-- Prove2me | Theorems.Thm_Formalism_UG_P_satake_subset_of_mem
-- name    : Formalism.UG.P.satake_subset_of_mem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:34:22.212617+00:00
-- url     : https://prove2.me/theorems/5962799d-3747-4999-a580-544cea58131b
-- title:
--   P: satake subset of mem
-- statement:
--   The P construction uses the satake subset of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SatakeMat.lean#L231-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SatakeMat.lean#L231-L238

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

theorem Formalism.UG.P.satake_subset_of_mem {π : L} (hπ : π ≠ 0) (hπO : π⁻¹ ∉ O) (S S' : Finset (Fin n))
    (c : satakePairs S → O) (c' : satakePairs S' → O)
    (h : (satakeGL O hπ S c)⁻¹ * satakeGL O hπ S' c' ∈ GLint (Fin n) O) : S ⊆ S' := by sorry
