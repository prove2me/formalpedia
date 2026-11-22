-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmLift_smul
-- name    : Formalism.BranchingDeterminantCap.bmLift_smul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:04:31.13445+00:00
-- url     : https://prove2.me/theorems/08e1b76a-3db5-4030-af33-befba31c884f
-- title:
--   Branching Determinant Cap: bm Lift smul
-- statement:
--   The Branching Determinant Cap construction uses the bm Lift smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1707-L1714
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1707-L1714

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

theorem Formalism.BranchingDeterminantCap.bmLift_smul {R : Type*} [CommRing R] {n : ℕ} {lam b : Fin n → ℕ} {f : MvPolynomial (Fin n × Fin n) R}
    {G : BP R n} (c : R) (h : bmLift R n lam b f G) : bmLift R n lam b (c • f) (c • G) := by sorry
