-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_HaP_map_mem
-- name    : Formalism.L2.FormalSeriesBounds.HaP.map_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:46:22.734809+00:00
-- url     : https://prove2.me/theorems/8d0a235c-6552-4366-b286-25ecac4492a3
-- title:
--   Ha P: map mem
-- statement:
--   The Ha P construction uses the map mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHaSpan.lean#L135-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHaSpan.lean#L135-L143

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

theorem Formalism.L2.FormalSeriesBounds.HaP.map_mem (hR : RowInvUpSt) (K : Type) [Field K] [CharZero K] (p : MvPolynomial (Letter Ty r n) ℚ)
    (hp : p ∈ HHa r n ℚ cc isX a) : map (algebraMap ℚ K) p ∈ HHa r n K cc isX a := by sorry
