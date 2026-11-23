-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_supd_mul
-- name    : Formalism.EigenvalueLevelCeiling.supd_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:55.590088+00:00
-- url     : https://prove2.me/theorems/22c00801-828b-45fa-9e94-231da711cc97
-- title:
--   Eigenvalue Level Ceiling: supd mul
-- statement:
--   The Eigenvalue Level Ceiling construction uses the supd mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/Mirabolic.lean#L197-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/Mirabolic.lean#L197-L213

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

theorem Formalism.EigenvalueLevelCeiling.supd_mul (u u' : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (hu : IsUniU u) (hu' : IsUniU u') :
    supd (u * u') = supd u + supd u' := by sorry
