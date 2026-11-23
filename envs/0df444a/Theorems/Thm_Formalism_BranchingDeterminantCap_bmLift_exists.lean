-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmLift_exists
-- name    : Formalism.BranchingDeterminantCap.bmLift_exists
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:24:47.682052+00:00
-- url     : https://prove2.me/theorems/47132070-1356-4fb1-a2ca-e813f5a7c560
-- title:
--   Branching Determinant Cap: bm Lift exists
-- statement:
--   The Branching Determinant Cap construction uses the bm Lift exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2188-L2204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2188-L2204

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

theorem Formalism.BranchingDeterminantCap.bmLift_exists {R : Type} [CommRing R] [IsDomain R] {n : ℕ} (lam sg : Fin n → ℕ) (hIL : bmIL lam sg)
    (f : MvPolynomial (Fin n × Fin n) R) (hf : f ∈ dualWeyl R n n sg) :
    ∃ G, bmLift R n lam (fun s => lam s - sg s) f G := by sorry
