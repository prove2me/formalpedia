-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_Zc
-- name    : Formalism.BranchingDeterminantCap.bmK_Zc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:02:35.497114+00:00
-- url     : https://prove2.me/theorems/7f974196-9f18-463f-a0a0-ffb460ec110a
-- title:
--   Branching Determinant Cap: bm K Zc
-- statement:
--   The Branching Determinant Cap construction uses the bm K Zc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2464-L2466
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2464-L2466

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

theorem Formalism.BranchingDeterminantCap.bmK_Zc (R : Type*) [CommRing R] (n : ℕ) (lam sg : Fin n → ℕ) (x : Module.End R (BP R n))
    (hx : ∀ i j, Commute x (bmEL R n i j)) : Commute x (bmZop R n lam sg) := by sorry
