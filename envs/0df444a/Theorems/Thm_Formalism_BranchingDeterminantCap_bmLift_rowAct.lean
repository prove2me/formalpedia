-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmLift_rowAct
-- name    : Formalism.BranchingDeterminantCap.bmLift_rowAct
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:40:47.605199+00:00
-- url     : https://prove2.me/theorems/6450d4ff-a149-4e9d-8020-e5ab68dc6acd
-- title:
--   Branching Determinant Cap: bm Lift row Act
-- statement:
--   The Branching Determinant Cap construction uses the bm Lift row Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1971-L1977
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1971-L1977

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

theorem Formalism.BranchingDeterminantCap.bmLift_rowAct {R : Type} [CommRing R] {n : ℕ} {lam b : Fin n → ℕ} {f : MvPolynomial (Fin n × Fin n) R}
    {G : BP R n} (g : Matrix (Fin n) (Fin n) R) (h : bmLift R n lam b f G) :
    bmLift R n lam b (rowAct R g f) (rowAct R (extM R g) G) := by sorry
