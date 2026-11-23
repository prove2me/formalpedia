-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bm_lastcomp_comm_bmEL
-- name    : Formalism.BranchingDeterminantCap.bm_lastcomp_comm_bmEL
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:25:14.958789+00:00
-- url     : https://prove2.me/theorems/a3ffb92f-2d3e-4242-b551-f001ff4626bb
-- title:
--   Branching Determinant Cap: bm lastcomp comm bm EL
-- statement:
--   The Branching Determinant Cap construction uses the bm lastcomp comm bm EL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L260-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L260-L262

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

theorem Formalism.BranchingDeterminantCap.bm_lastcomp_comm_bmEL (R : Type*) [CommRing R] (n : ℕ) (d : ℕ) (s t : Fin n) :
    Commute (weightedHomogeneousComponent (lastW n) d : Module.End R (BP R n)) (bmEL R n s t) := by sorry
