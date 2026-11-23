-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_pair_comm
-- name    : Formalism.EigenvalueLevelCeiling.pair_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:44.660829+00:00
-- url     : https://prove2.me/theorems/21c84015-a625-4228-bafc-8be02ed12859
-- title:
--   Eigenvalue Level Ceiling: pair comm
-- statement:
--   The Eigenvalue Level Ceiling construction uses the pair comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/Mirabolic.lean#L35-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/Mirabolic.lean#L35-L46

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_Mirabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.EigenvalueLevelCeiling
variable {k : Type} [Field k] {n : ℕ}

theorem Formalism.EigenvalueLevelCeiling.pair_comm (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (s l : Fin n) (t : k) :
    pairU h s l t * h = h * pairV h s l t := by sorry
