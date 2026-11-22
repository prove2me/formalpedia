-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmLift_minor1
-- name    : Formalism.BranchingDeterminantCap.bmLift_minor1
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:03:06.551238+00:00
-- url     : https://prove2.me/theorems/acc5180e-39de-4f40-ac00-51d25a2ef3de
-- title:
--   Branching Determinant Cap: bm Lift minor1
-- statement:
--   The Branching Determinant Cap construction uses the bm Lift minor1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1822-L1874
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1822-L1874

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

theorem Formalism.BranchingDeterminantCap.bmLift_minor1 (R : Type*) [CommRing R] (n : ℕ) {s : ℕ} (I : Fin s → Fin n) (hs : s + 1 ≤ n) :
    bmLift R n (initW n (s + 1)) (Pi.single ⟨s, hs⟩ 1) (initMinor R I (Nat.le_of_succ_le hs))
      (initMinor R (fun p : Fin (s + 1) => if h : p.val < s then (I ⟨p.val, h⟩).castSucc else Fin.last n) hs) := by sorry
