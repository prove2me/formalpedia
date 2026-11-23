-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmH_flatMap_prod
-- name    : Formalism.BranchingDeterminantCap.bmH_flatMap_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:24:57.652175+00:00
-- url     : https://prove2.me/theorems/dfd963c7-7242-4437-bef2-293b063604a8
-- title:
--   Branching Determinant Cap: bm H flat Map prod
-- statement:
--   The Branching Determinant Cap construction uses the bm H flat Map prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1357-L1361
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1357-L1361

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod

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

theorem Formalism.BranchingDeterminantCap.bmH_flatMap_prod {α : Type*} (l : List α) (f : α → List ℤ) (g : ℤ → ℤ) :
    ((l.flatMap f).map g).prod = (l.map fun i => ((f i).map g).prod).prod := by sorry
