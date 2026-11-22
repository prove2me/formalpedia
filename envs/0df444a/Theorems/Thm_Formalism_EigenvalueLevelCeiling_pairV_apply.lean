-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_pairV_apply
-- name    : Formalism.EigenvalueLevelCeiling.pairV_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:09:36.375654+00:00
-- url     : https://prove2.me/theorems/22cae0a8-8f6c-42f3-a0f9-8c987e1bdacc
-- title:
--   Eigenvalue Level Ceiling: pair V apply
-- statement:
--   The Eigenvalue Level Ceiling construction uses the pair V apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/Mirabolic.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/Mirabolic.lean#L30-L33

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

theorem Formalism.EigenvalueLevelCeiling.pairV_apply (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (s l : Fin n) (t : k) (a b) :
    pairV h s l t a b = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b +
      t * ((if a = l.castSucc then 1 else 0) * h s.succ b) := by sorry
