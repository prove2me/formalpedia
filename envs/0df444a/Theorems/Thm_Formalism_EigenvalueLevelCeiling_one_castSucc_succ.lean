-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_one_castSucc_succ
-- name    : Formalism.EigenvalueLevelCeiling.one_castSucc_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:09:44.329032+00:00
-- url     : https://prove2.me/theorems/841a6733-382f-4504-9080-20499b6a351a
-- title:
--   Eigenvalue Level Ceiling: one cast Succ succ
-- statement:
--   The Eigenvalue Level Ceiling construction uses the one cast Succ succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/Mirabolic.lean#L90-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/Mirabolic.lean#L90-L92

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

theorem Formalism.EigenvalueLevelCeiling.one_castSucc_succ (a : Fin n) :
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a.castSucc a.succ = 0 := by sorry
