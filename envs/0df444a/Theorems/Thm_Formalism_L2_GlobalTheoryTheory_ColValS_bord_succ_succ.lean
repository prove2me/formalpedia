-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_ColValS_bord_succ_succ
-- name    : Formalism.L2.GlobalTheoryTheory.ColValS.bord_succ_succ
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:18:58.672805+00:00
-- url     : https://prove2.me/theorems/bf1f49b5-3bb4-427b-9db1-8329b618aac7
-- title:
--   Col Val S: bord succ succ
-- statement:
--   The Col Val S construction uses the bord succ succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/ElemZeroZeroMulApply.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/ElemZeroZeroMulApply.lean#L25-L27

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

theorem Formalism.L2.GlobalTheoryTheory.ColValS.bord_succ_succ {m : ℕ} (M : Matrix (Fin m) (Fin m) O) (i j : Fin m) :
    bord M i.succ j.succ = M i j := by sorry
