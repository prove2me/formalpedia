-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_Zz
-- name    : Formalism.BranchingDeterminantCap.bmK_Zz
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:24:23.972522+00:00
-- url     : https://prove2.me/theorems/71481ca7-00ec-418d-bf10-79ae28cfe748
-- title:
--   Branching Determinant Cap: bm K Zz
-- statement:
--   The Branching Determinant Cap construction uses the bm K Zz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2468-L2470
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2468-L2470

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

theorem Formalism.BranchingDeterminantCap.bmK_Zz (R : Type*) [CommRing R] (n : ℕ) (lam sg : Fin n → ℕ) (β : Fin n → ℤ) (G : BP R n) :
    zcomp R n β (bmZop R n lam sg G) = bmZop R n lam sg (zcomp R n β G) := by sorry
