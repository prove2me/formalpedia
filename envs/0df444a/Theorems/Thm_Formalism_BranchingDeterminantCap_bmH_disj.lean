-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmH_disj
-- name    : Formalism.BranchingDeterminantCap.bmH_disj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:24:35.952638+00:00
-- url     : https://prove2.me/theorems/6b3c1791-fa17-4498-91de-9078f98bae84
-- title:
--   Branching Determinant Cap: bm H disj
-- statement:
--   The Branching Determinant Cap construction uses the bm H disj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1280-L1299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1280-L1299

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

theorem Formalism.BranchingDeterminantCap.bmH_disj {n : ℕ} (L : Fin (n + 1) → ℤ) (μ ν : Fin n → ℤ) (hμ : Interlace L μ) (hν : Interlace L ν)
    (i j : Fin n) (hij : i ≠ j) : (ν i - ((i : ℕ) : ℤ)) - (μ j - ((j : ℕ) : ℤ)) ≠ 0 := by sorry
