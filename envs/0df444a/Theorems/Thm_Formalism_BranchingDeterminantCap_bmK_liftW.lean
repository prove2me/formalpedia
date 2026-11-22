-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_liftW
-- name    : Formalism.BranchingDeterminantCap.bmK_liftW
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:04:33.017973+00:00
-- url     : https://prove2.me/theorems/d8f9ba99-7659-42a3-addd-af8968fea27a
-- title:
--   Branching Determinant Cap: bm K lift W
-- statement:
--   The Branching Determinant Cap construction uses the bm K lift W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2493-L2495
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2493-L2495

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

theorem Formalism.BranchingDeterminantCap.bmK_liftW {R : Type*} [CommRing R] {n : ℕ} {lam b : Fin n → ℕ} {f : MvPolynomial (Fin n × Fin n) R}
    {G : BP R n} (h : bmLift R n lam b f G) : G ∈ bmW R n lam (∑ s, b s) := by sorry
