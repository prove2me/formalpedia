-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_xn_cof_supported
-- name    : Formalism.BranchingDeterminantCap.xn_cof_supported
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:08.974864+00:00
-- url     : https://prove2.me/theorems/49524d2b-b77d-44a1-b279-a37ffa64b438
-- title:
--   Branching Determinant Cap: xn cof supported
-- statement:
--   The Branching Determinant Cap construction uses the xn cof supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/XiNorm.lean#L70-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/XiNorm.lean#L70-L77

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockbLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_XiNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.REAL
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
variable {r n : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]

theorem Formalism.BranchingDeterminantCap.xn_cof_supported (ι : κ → Fin r) {p : ℕ} (hp : p + 1 ≤ n) (a : Fin p → κ) (j : Fin (p + 1)) :
    xnCof ι hp a j ∈ supported ℂ {v : Fin r × Fin n | ∃ i, v.1 = ι (a i)} := by sorry
