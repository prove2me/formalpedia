-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_rowAct_var_WH
-- name    : Formalism.BranchingDeterminantCap.bmF_rowAct_var_WH
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:23:34.749199+00:00
-- url     : https://prove2.me/theorems/ee490df5-1fc5-40b5-b02c-f2f59b348a32
-- title:
--   Branching Determinant Cap: bm F row Act var WH
-- statement:
--   The Branching Determinant Cap construction uses the bm F row Act var WH property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1915-L1940
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1915-L1940

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

theorem Formalism.BranchingDeterminantCap.bmF_rowAct_var_WH (R : Type*) [CommRing R] {n : ℕ} {B : Type*} [AddCommMonoid B]
    (w : Fin (n + 1) × Fin n → B) (hw : ∀ a b s : Fin n, w (a.castSucc, s) = w (b.castSucc, s))
    (g : Matrix (Fin n) (Fin n) R) (v : Fin (n + 1) × Fin n) :
    IsWeightedHomogeneous w (∑ b : Fin (n + 1), C (extM R g v.1 b) * (X (b, v.2) : BP R n)) (w v) := by sorry
