-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_ColValS_bord_succ_zero
-- name    : Formalism.L2.GlobalTheoryTheory.ColValS.bord_succ_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:18:33.342924+00:00
-- url     : https://prove2.me/theorems/61257ecb-d72c-4074-8683-b5a27fed3dc8
-- title:
--   Col Val S: bord succ zero
-- statement:
--   The Col Val S construction uses the bord succ zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/ElemZeroZeroMulApply.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/ElemZeroZeroMulApply.lean#L22-L24

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_ElemZeroZeroMulApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.ColValS
open Matrix
variable {O : Type} [CommRing O]

theorem Formalism.L2.GlobalTheoryTheory.ColValS.bord_succ_zero {m : ℕ} (M : Matrix (Fin m) (Fin m) O) (i : Fin m) :
    bord M i.succ 0 = 0 := by sorry
