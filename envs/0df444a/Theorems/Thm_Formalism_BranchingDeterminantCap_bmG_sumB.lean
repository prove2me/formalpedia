-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_sumB
-- name    : Formalism.BranchingDeterminantCap.bmG_sumB
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:24:27.550393+00:00
-- url     : https://prove2.me/theorems/41415568-8578-479d-b6f9-5bc50739aefe
-- title:
--   Branching Determinant Cap: bm G sum B
-- statement:
--   The Branching Determinant Cap construction uses the bm G sum B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2328-L2340
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2328-L2340

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

theorem Formalism.BranchingDeterminantCap.bmG_sumB {n : ℕ} (i : Fin n) :
    (∑ p : Fin (i.val + 1), (Pi.single (rowsB i p) 1 : Fin (n + 1) → ℕ)) =
      initW (n + 1) i.val + Pi.single (Fin.last n) 1 := by sorry
