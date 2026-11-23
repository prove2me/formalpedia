-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bm_list_prod
-- name    : Formalism.BranchingDeterminantCap.bm_list_prod
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:24:59.530517+00:00
-- url     : https://prove2.me/theorems/4d61a26f-f27e-48d6-b264-6a4a919fbae2
-- title:
--   Branching Determinant Cap: bm list prod
-- statement:
--   The Branching Determinant Cap construction uses the bm list prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1363-L1377
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1363-L1377

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

theorem Formalism.BranchingDeterminantCap.bm_list_prod {n : ℕ} (lam sg : Fin n → ℕ) (hI : Interlace (lamZ lam) (fun i => (sg i : ℤ))) :
    ((bmList lam sg).map (bmChi lam fun s => ((lam s - sg s : ℕ) : ℤ))).prod =
      cCap (lamZ lam) (fun i => (sg i : ℤ)) := by sorry
