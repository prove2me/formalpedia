-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_pairU_apply
-- name    : Formalism.EigenvalueLevelCeiling.pairU_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:40:42.623808+00:00
-- url     : https://prove2.me/theorems/8782a2cb-caf8-4d6f-a9c3-a1a36e22b7e3
-- title:
--   Eigenvalue Level Ceiling: pair U apply
-- statement:
--   The Eigenvalue Level Ceiling construction uses the pair U apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/Mirabolic.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/Mirabolic.lean#L25-L28

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

theorem Formalism.EigenvalueLevelCeiling.pairU_apply (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (s l : Fin n) (t : k) (a b) :
    pairU h s l t a b = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b +
      t * (h a l.castSucc * if b = s.succ then 1 else 0) := by sorry
