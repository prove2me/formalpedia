-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmC_pderiv_colAddGen_X
-- name    : Formalism.BranchingDeterminantCap.bmC_pderiv_colAddGen_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:20:21.663427+00:00
-- url     : https://prove2.me/theorems/27b30289-84ec-4ae3-bdfb-0b2c37421739
-- title:
--   Branching Determinant Cap: bm C pderiv col Add Gen X
-- statement:
--   The Branching Determinant Cap construction uses the bm C pderiv col Add Gen X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L920-L925
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L920-L925

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

theorem Formalism.BranchingDeterminantCap.bmC_pderiv_colAddGen_X {R : Type*} [CommRing R] {r n : ℕ} {l j : Fin n} (hlj : l ≠ j)
    (v : Fin r × Fin n) :
    pderiv none (colAddGen R l j (X v)) = colAddGen R l j (ndE R r n l j (X v)) := by sorry
