-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_supd_pairV
-- name    : Formalism.EigenvalueLevelCeiling.supd_pairV
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:46.129199+00:00
-- url     : https://prove2.me/theorems/f2ad0750-2658-4b55-98dd-e30e049f5283
-- title:
--   Eigenvalue Level Ceiling: supd pair V
-- statement:
--   The Eigenvalue Level Ceiling construction uses the supd pair V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/Mirabolic.lean#L98-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/Mirabolic.lean#L98-L100

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

theorem Formalism.EigenvalueLevelCeiling.supd_pairV (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (s l : Fin n) (t : k) :
    supd (pairV h s l t) = t * h s.succ l.succ := by sorry
