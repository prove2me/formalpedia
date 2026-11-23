-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_supd_one
-- name    : Formalism.EigenvalueLevelCeiling.supd_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:57.129853+00:00
-- url     : https://prove2.me/theorems/b99c8b0f-82a4-4816-9896-40d2d4920094
-- title:
--   Eigenvalue Level Ceiling: supd one
-- statement:
--   The Eigenvalue Level Ceiling construction uses the supd one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/Mirabolic.lean#L194-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/Mirabolic.lean#L194-L195

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

theorem Formalism.EigenvalueLevelCeiling.supd_one : supd (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = 0 := by sorry
