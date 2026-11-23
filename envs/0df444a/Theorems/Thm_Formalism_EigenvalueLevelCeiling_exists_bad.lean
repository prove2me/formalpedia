-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_exists_bad
-- name    : Formalism.EigenvalueLevelCeiling.exists_bad
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:31:35.821354+00:00
-- url     : https://prove2.me/theorems/76b78d92-1d86-4a92-aef3-3786b02f2b41
-- title:
--   Eigenvalue Level Ceiling: exists bad
-- statement:
--   The Eigenvalue Level Ceiling construction uses the exists bad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/Mirabolic.lean#L102-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/Mirabolic.lean#L102-L146

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

theorem Formalism.EigenvalueLevelCeiling.exists_bad (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (hm : IsMirab h) (hu : ¬ IsUniU h) :
    ∃ s l : Fin n, l ≤ s ∧ (∀ j, s.castSucc < j → h j j = 1 ∧ ∀ b, b < j → h j b = 0) ∧
      h s.castSucc l.castSucc ≠ if l = s then 1 else 0 := by sorry
