-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_choose_succ_mul_two_pow_le
-- name    : Formalism.BranchingDeterminantCap.choose_succ_mul_two_pow_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:26:32.108049+00:00
-- url     : https://prove2.me/theorems/90454c31-f755-4b99-89e5-5870410b3665
-- title:
--   Branching Determinant Cap: choose succ mul two pow le
-- statement:
--   The Branching Determinant Cap construction uses the choose succ mul two pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Numeric.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/Numeric.lean#L16-L20

import Definitions.Def_Formalism_BranchSandwichDivisors_NormLog
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Interlace
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Numeric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.BranchingDeterminantCap

theorem Formalism.BranchingDeterminantCap.choose_succ_mul_two_pow_le (r j : ℕ) : r.choose (j + 1) * 2 ^ j ≤ r ^ (j + 1) := by sorry
