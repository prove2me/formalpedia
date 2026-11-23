-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmLift_minor0
-- name    : Formalism.BranchingDeterminantCap.bmLift_minor0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:23:10.911773+00:00
-- url     : https://prove2.me/theorems/95484312-9734-4a1a-a26d-cc980f1bd801
-- title:
--   Branching Determinant Cap: bm Lift minor0
-- statement:
--   The Branching Determinant Cap construction uses the bm Lift minor0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1778-L1789
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1778-L1789

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

theorem Formalism.BranchingDeterminantCap.bmLift_minor0 (R : Type*) [CommRing R] (n : ℕ) {s : ℕ} (I : Fin s → Fin n) (hs : s ≤ n) :
    bmLift R n (initW n s) 0 (initMinor R I hs) (initMinor R (fun p => (I p).castSucc) hs) := by sorry
