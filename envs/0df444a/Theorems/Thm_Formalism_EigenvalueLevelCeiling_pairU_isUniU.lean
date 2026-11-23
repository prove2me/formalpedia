-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_pairU_isUniU
-- name    : Formalism.EigenvalueLevelCeiling.pairU_isUniU
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:25.121689+00:00
-- url     : https://prove2.me/theorems/b82eea16-18c0-4429-922c-7bfb216e1a51
-- title:
--   Eigenvalue Level Ceiling: pair U is Uni U
-- statement:
--   The Eigenvalue Level Ceiling construction uses the pair U is Uni U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/Mirabolic.lean#L48-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/Mirabolic.lean#L48-L67

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

theorem Formalism.EigenvalueLevelCeiling.pairU_isUniU (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (s l : Fin n) (hl : l ≤ s)
    (hg : ∀ j, s.castSucc < j → ∀ b, b < j → h j b = 0) (t : k) : IsUniU (pairU h s l t) := by sorry
