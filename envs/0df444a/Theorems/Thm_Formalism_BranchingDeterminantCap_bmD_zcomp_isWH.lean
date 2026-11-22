-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmD_zcomp_isWH
-- name    : Formalism.BranchingDeterminantCap.bmD_zcomp_isWH
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:22:16.254805+00:00
-- url     : https://prove2.me/theorems/9233ebc5-8358-4db6-9417-80906c8714d6
-- title:
--   Branching Determinant Cap: bm D zcomp is WH
-- statement:
--   The Branching Determinant Cap construction uses the bm D zcomp is WH property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1389-L1391
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1389-L1391

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

theorem Formalism.BranchingDeterminantCap.bmD_zcomp_isWH {R : Type*} [CommRing R] {n : ℕ} (β : Fin n → ℤ) (Y : BP R n) :
    IsWeightedHomogeneous (zW n) (zcomp R n β Y) β := by sorry
