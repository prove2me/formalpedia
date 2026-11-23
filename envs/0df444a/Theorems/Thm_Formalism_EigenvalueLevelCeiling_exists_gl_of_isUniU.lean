-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_exists_gl_of_isUniU
-- name    : Formalism.EigenvalueLevelCeiling.exists_gl_of_isUniU
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:31:41.095289+00:00
-- url     : https://prove2.me/theorems/5c3edd55-9581-4e72-a889-cec1a93a7130
-- title:
--   Eigenvalue Level Ceiling: exists gl of is Uni U
-- statement:
--   The Eigenvalue Level Ceiling construction uses the exists gl of is Uni U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/Mirabolic.lean#L10-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/Mirabolic.lean#L10-L15

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

theorem Formalism.EigenvalueLevelCeiling.exists_gl_of_isUniU (M : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (hM : IsUniU M) :
    ∃ g : GL (Fin (n + 1)) k, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = M := by sorry
