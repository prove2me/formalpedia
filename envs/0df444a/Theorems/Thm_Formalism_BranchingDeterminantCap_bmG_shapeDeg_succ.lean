-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_shapeDeg_succ
-- name    : Formalism.BranchingDeterminantCap.bmG_shapeDeg_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:24:20.095099+00:00
-- url     : https://prove2.me/theorems/a224f013-e88a-4d22-a78e-a20ee97d387f
-- title:
--   Branching Determinant Cap: bm G shape Deg succ
-- statement:
--   The Branching Determinant Cap construction uses the bm G shape Deg succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2002-L2004
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2002-L2004

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

theorem Formalism.BranchingDeterminantCap.bmG_shapeDeg_succ {n K : ℕ} (sz : Fin (K + 1) → ℕ) (t : Fin n) :
    shapeDeg sz t = (if t.val < sz 0 then 1 else 0) + shapeDeg (fun k : Fin K => sz k.succ) t := by sorry
