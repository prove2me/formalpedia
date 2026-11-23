-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_shapeDeg_zero
-- name    : Formalism.BranchingDeterminantCap.bmG_shapeDeg_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:24:34.354469+00:00
-- url     : https://prove2.me/theorems/40443095-4c01-4971-a339-1b1f44094ca6
-- title:
--   Branching Determinant Cap: bm G shape Deg zero
-- statement:
--   The Branching Determinant Cap construction uses the bm G shape Deg zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2006-L2008
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2006-L2008

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap

theorem Formalism.BranchingDeterminantCap.bmG_shapeDeg_zero {n : ℕ} (sz : Fin 0 → ℕ) : (shapeDeg sz : Fin n → ℕ) = 0 := by sorry
