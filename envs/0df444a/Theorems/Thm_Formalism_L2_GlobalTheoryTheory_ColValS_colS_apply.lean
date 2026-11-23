-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_ColValS_colS_apply
-- name    : Formalism.L2.GlobalTheoryTheory.ColValS.colS_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:19:12.625336+00:00
-- url     : https://prove2.me/theorems/4be23237-1b03-4f1b-b7a9-028a5fa523e4
-- title:
--   Col Val S: col S apply
-- statement:
--   The Col Val S construction uses the col S apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/ElemZeroZeroMulApply.lean#L37-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/ElemZeroZeroMulApply.lean#L37-L44

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

theorem Formalism.L2.GlobalTheoryTheory.ColValS.colS_apply {m : ℕ} (f : Fin m → O) (i j : Fin (m+1)) :
    colS f i j = (1 : Matrix (Fin (m+1)) (Fin (m+1)) O) i j +
      Fin.cases 0 (fun k => if j = 0 then f k else 0) i := by sorry
