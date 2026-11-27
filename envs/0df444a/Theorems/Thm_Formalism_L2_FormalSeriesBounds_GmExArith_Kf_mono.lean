-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_Kf_mono
-- name    : Formalism.L2.FormalSeriesBounds.GmExArith.Kf_mono
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-27T05:09:46.94165+00:00
-- url     : https://prove2.me/theorems/a9c13afb-41a0-5ac9-9728-6b9608321a62
-- title:
--   Gm Ex Arith: Kf mono
-- statement:
--   The Gm Ex Arith construction uses the Kf mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePGmExLem.lean#L213-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePGmExLem.lean#L213-L215

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SelfConjugateRowData
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePGmExLem
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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.GmExArith
open Formalism.L2.FormalSeriesBounds NumberField
variable {C : Type} [Field C] {V : VF C}

theorem Formalism.L2.FormalSeriesBounds.GmExArith.Kf_mono {ε : ℝ} (hε : 0 < ε) {n m : ℕ} (h : n ≤ m) : Kf ε n ≤ Kf ε m := by sorry
