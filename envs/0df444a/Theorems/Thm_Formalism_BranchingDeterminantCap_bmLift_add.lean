-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmLift_add
-- name    : Formalism.BranchingDeterminantCap.bmLift_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:02:44.278968+00:00
-- url     : https://prove2.me/theorems/bdedfe73-8a5c-4f2d-b628-a55de6b68dea
-- title:
--   Branching Determinant Cap: bm Lift add
-- statement:
--   The Branching Determinant Cap construction uses the bm Lift add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1694-L1705
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1694-L1705

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

theorem Formalism.BranchingDeterminantCap.bmLift_add {R : Type*} [CommRing R] {n : ℕ} {lam b : Fin n → ℕ} {f f' : MvPolynomial (Fin n × Fin n) R}
    {G G' : BP R n} (h : bmLift R n lam b f G) (h' : bmLift R n lam b f' G') :
    bmLift R n lam b (f + f') (G + G') := by sorry
