-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_emb_X
-- name    : Formalism.BranchingDeterminantCap.bmF_emb_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:22:01.438692+00:00
-- url     : https://prove2.me/theorems/b153c7a0-22ad-4334-bff2-e6f43e85214f
-- title:
--   Branching Determinant Cap: bm F emb X
-- statement:
--   The Branching Determinant Cap construction uses the bm F emb X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1766-L1768
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1766-L1768

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

theorem Formalism.BranchingDeterminantCap.bmF_emb_X (R : Type*) [CommRing R] (n : ℕ) (v : Fin n × Fin n) :
    emb R n (X v) = X (v.1.castSucc, v.2) := by sorry
