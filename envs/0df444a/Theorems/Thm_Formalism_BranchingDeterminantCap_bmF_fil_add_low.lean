-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_fil_add_low
-- name    : Formalism.BranchingDeterminantCap.bmF_fil_add_low
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:21:48.285794+00:00
-- url     : https://prove2.me/theorems/43b35695-0398-4a85-8711-c510b220ca8c
-- title:
--   Branching Determinant Cap: bm F fil add low
-- statement:
--   The Branching Determinant Cap construction uses the bm F fil add low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1643-L1648
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1643-L1648

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

theorem Formalism.BranchingDeterminantCap.bmF_fil_add_low {R : Type*} [CommRing R] {n : ℕ} {D : ℤ} {F L : BP R n} (hF : bmF_Fil D F)
    (hL : IsLow D L) : bmF_Fil D (F + L) := by sorry
