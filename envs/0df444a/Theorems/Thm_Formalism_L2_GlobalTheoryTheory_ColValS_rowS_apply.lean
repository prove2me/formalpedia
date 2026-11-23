-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_ColValS_rowS_apply
-- name    : Formalism.L2.GlobalTheoryTheory.ColValS.rowS_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:19:27.01738+00:00
-- url     : https://prove2.me/theorems/eb07b8a9-6da1-4724-8806-3792701c5b6c
-- title:
--   Col Val S: row S apply
-- statement:
--   The Col Val S construction uses the row S apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/ElemZeroZeroMulApply.lean#L46-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/ElemZeroZeroMulApply.lean#L46-L53

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

theorem Formalism.L2.GlobalTheoryTheory.ColValS.rowS_apply {m : ℕ} (g : Fin m → O) (i j : Fin (m+1)) :
    rowS g i j = (1 : Matrix (Fin (m+1)) (Fin (m+1)) O) i j +
      Fin.cases 0 (fun k => if i = 0 then g k else 0) j := by sorry
