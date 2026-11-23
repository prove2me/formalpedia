-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_lead_WH
-- name    : Formalism.BranchingDeterminantCap.bmF_lead_WH
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:37.425043+00:00
-- url     : https://prove2.me/theorems/05362b28-705c-40f1-ae98-5eb10dd9e131
-- title:
--   Branching Determinant Cap: bm F lead WH
-- statement:
--   The Branching Determinant Cap construction uses the bm F lead WH property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1690-L1692
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1690-L1692

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

theorem Formalism.BranchingDeterminantCap.bmF_lead_WH (R : Type*) [CommRing R] (n : ℕ) (b : Fin n → ℕ) (f : MvPolynomial (Fin n × Fin n) R) :
    IsWeightedHomogeneous (zW n) (zmon R n b * emb R n f) (fun s => (b s : ℤ)) := by sorry
