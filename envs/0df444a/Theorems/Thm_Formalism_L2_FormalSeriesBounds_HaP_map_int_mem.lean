-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_HaP_map_int_mem
-- name    : Formalism.L2.FormalSeriesBounds.HaP.map_int_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:47:45.32722+00:00
-- url     : https://prove2.me/theorems/15274e81-334e-4571-ada3-6cc82335a011
-- title:
--   Ha P: map int mem
-- statement:
--   The Ha P construction uses the map int mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHaSpan.lean#L145-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHaSpan.lean#L145-L150

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaDefs
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescSpanSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.HaP
open MvPolynomial Formalism.L2.Pj
variable {Ty : Type} {r : Ty → ℕ} {n : ℕ} {cc : Ty → Ty} {isX : Ty → Prop} {a : Ty → ℕ → ℕ}

theorem Formalism.L2.FormalSeriesBounds.HaP.map_int_mem (hR : RowInvUpSt) (K : Type) [Field K] [CharZero K] (z : MvPolynomial (Letter Ty r n) ℤ)
    (hz : map (Int.castRingHom ℚ) z ∈ HHa r n ℚ cc isX a) : map (Int.castRingHom K) z ∈ HHa r n K cc isX a := by sorry
