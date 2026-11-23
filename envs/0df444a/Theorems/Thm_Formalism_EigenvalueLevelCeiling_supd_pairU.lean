-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_supd_pairU
-- name    : Formalism.EigenvalueLevelCeiling.supd_pairU
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:26.477209+00:00
-- url     : https://prove2.me/theorems/1d9b5abf-0474-4858-9f28-636a22d6ab47
-- title:
--   Eigenvalue Level Ceiling: supd pair U
-- statement:
--   The Eigenvalue Level Ceiling construction uses the supd pair U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/Mirabolic.lean#L94-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/Mirabolic.lean#L94-L96

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

theorem Formalism.EigenvalueLevelCeiling.supd_pairU (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (s l : Fin n) (t : k) :
    supd (pairU h s l t) = t * h s.castSucc l.castSucc := by sorry
