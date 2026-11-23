-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_ColValS_zero_eq_succ_iff
-- name    : Formalism.L2.GlobalTheoryTheory.ColValS.zero_eq_succ_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:19:05.978828+00:00
-- url     : https://prove2.me/theorems/8a2ddde7-8226-46fb-b775-fe683de57b04
-- title:
--   Col Val S: zero eq succ iff
-- statement:
--   The Col Val S construction uses the zero eq succ iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/ElemZeroZeroMulApply.lean#L29-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/ElemZeroZeroMulApply.lean#L29-L29

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

theorem Formalism.L2.GlobalTheoryTheory.ColValS.zero_eq_succ_iff {m : ℕ} (k : Fin m) : ((0 : Fin (m+1)) = k.succ) ↔ False := by sorry
