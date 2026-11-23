-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_xn_E_X
-- name    : Formalism.BranchingDeterminantCap.xn_E_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:06.395779+00:00
-- url     : https://prove2.me/theorems/250f01ac-ba6c-4fca-bd8a-beb69938bc61
-- title:
--   Branching Determinant Cap: xn E X
-- statement:
--   The Branching Determinant Cap construction uses the xn E X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/XiNorm.lean#L511-L519
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/XiNorm.lean#L511-L519

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
variable {r n : ℕ}

theorem Formalism.BranchingDeterminantCap.xn_E_X (t s : Fin n) (v : Fin r × Fin n) :
    ∑ b : Fin r, (X (b, t) : MvPolynomial (Fin r × Fin n) ℂ) * pderiv (b, s) (X v) =
      if v.2 = s then X (v.1, t) else 0 := by sorry
