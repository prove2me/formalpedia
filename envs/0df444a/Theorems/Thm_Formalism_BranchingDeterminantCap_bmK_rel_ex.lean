-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_rel_ex
-- name    : Formalism.BranchingDeterminantCap.bmK_rel_ex
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:23:05.177471+00:00
-- url     : https://prove2.me/theorems/d70254f8-bcf5-48e2-8ee4-059eb652e7b5
-- title:
--   Branching Determinant Cap: bm K rel ex
-- statement:
--   The Branching Determinant Cap construction uses the bm K rel ex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2595-L2597
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2595-L2597

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

theorem Formalism.BranchingDeterminantCap.bmK_rel_ex {R : Type} [CommRing R] [IsDomain R] {n : ℕ} (lam sg : Fin n → ℕ)
    (hIL : bmIL lam sg) (f : ↥(dualWeyl R n n sg)) : ∃ G, bmRel R n lam sg f G := by sorry
