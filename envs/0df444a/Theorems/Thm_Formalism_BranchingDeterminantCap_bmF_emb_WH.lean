-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_emb_WH
-- name    : Formalism.BranchingDeterminantCap.bmF_emb_WH
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:01:44.180413+00:00
-- url     : https://prove2.me/theorems/7e908b1d-b9e7-43d9-affc-bc5af87173cd
-- title:
--   Branching Determinant Cap: bm F emb WH
-- statement:
--   The Branching Determinant Cap construction uses the bm F emb WH property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1667-L1682
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1667-L1682

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

theorem Formalism.BranchingDeterminantCap.bmF_emb_WH {R : Type*} [CommRing R] {n : ℕ} {B : Type*} [AddCommMonoid B]
    (w : Fin (n + 1) × Fin n → B) (hw : ∀ (a : Fin n) (s : Fin n), w (a.castSucc, s) = 0)
    (f : MvPolynomial (Fin n × Fin n) R) : IsWeightedHomogeneous w (emb R n f) 0 := by sorry
