-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmC_pderiv_colAddGen
-- name    : Formalism.BranchingDeterminantCap.bmC_pderiv_colAddGen
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:20:46.272481+00:00
-- url     : https://prove2.me/theorems/078fca72-1af9-408e-8be1-359b7c2bd7cd
-- title:
--   Branching Determinant Cap: bm C pderiv col Add Gen
-- statement:
--   The Branching Determinant Cap construction uses the bm C pderiv col Add Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L927-L933
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L927-L933

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

theorem Formalism.BranchingDeterminantCap.bmC_pderiv_colAddGen {R : Type*} [CommRing R] {r n : ℕ} {l j : Fin n} (hlj : l ≠ j)
    (g : MvPolynomial (Fin r × Fin n) R) :
    pderiv none (colAddGen R l j g) = colAddGen R l j (ndE R r n l j g) := by sorry
