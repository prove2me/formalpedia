-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_rel_smul
-- name    : Formalism.BranchingDeterminantCap.bmK_rel_smul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:24:44.146169+00:00
-- url     : https://prove2.me/theorems/87c3a4ce-fcb1-4286-9261-ab3d25f3c82b
-- title:
--   Branching Determinant Cap: bm K rel smul
-- statement:
--   The Branching Determinant Cap construction uses the bm K rel smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2604-L2606
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2604-L2606

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

theorem Formalism.BranchingDeterminantCap.bmK_rel_smul {R : Type} [CommRing R] {n : ℕ} (lam sg : Fin n → ℕ) (c : R) (f : ↥(dualWeyl R n n sg))
    (G : BP R n) (h : bmRel R n lam sg f G) : bmRel R n lam sg (c • f) (c • G) := by sorry
