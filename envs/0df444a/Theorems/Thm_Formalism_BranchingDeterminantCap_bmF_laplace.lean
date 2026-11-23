-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_laplace
-- name    : Formalism.BranchingDeterminantCap.bmF_laplace
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:00.243326+00:00
-- url     : https://prove2.me/theorems/073a997e-11f8-4f80-a6a0-a0eae1455e40
-- title:
--   Branching Determinant Cap: bm F laplace
-- statement:
--   The Branching Determinant Cap construction uses the bm F laplace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1806-L1820
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1806-L1820

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

theorem Formalism.BranchingDeterminantCap.bmF_laplace (R : Type*) [CommRing R] (n : ℕ) {s : ℕ} (I : Fin s → Fin n) (hs : s + 1 ≤ n) :
    initMinor R (fun p : Fin (s + 1) => if h : p.val < s then (I ⟨p.val, h⟩).castSucc else Fin.last n) hs =
      ∑ j : Fin (s + 1), (-1 : BP R n) ^ (s + (j : ℕ)) * X (Fin.last n, Fin.castLE hs j) *
        emb R n (Matrix.of fun p q : Fin s =>
          (X (I p, Fin.castLE hs (j.succAbove q)) : MvPolynomial (Fin n × Fin n) R)).det := by sorry
