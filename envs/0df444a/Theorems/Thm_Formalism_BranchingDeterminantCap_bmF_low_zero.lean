-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_low_zero
-- name    : Formalism.BranchingDeterminantCap.bmF_low_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:43:12.108543+00:00
-- url     : https://prove2.me/theorems/59ea810b-c116-418a-b7d5-3b5f4eca7eff
-- title:
--   Branching Determinant Cap: bm F low zero
-- statement:
--   The Branching Determinant Cap construction uses the bm F low zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1608-L1610
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1608-L1610

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

theorem Formalism.BranchingDeterminantCap.bmF_low_zero {R : Type*} [CommRing R] {n : ℕ} (D : ℤ) : IsLow D (0 : BP R n) := by sorry
