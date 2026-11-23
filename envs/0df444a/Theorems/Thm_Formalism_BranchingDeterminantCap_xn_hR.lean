-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_xn_hR
-- name    : Formalism.BranchingDeterminantCap.xn_hR
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:26:57.388396+00:00
-- url     : https://prove2.me/theorems/3cb3c642-fc6f-46b1-a7f1-a2c3e9d89f57
-- title:
--   Branching Determinant Cap: xn h R
-- statement:
--   The Branching Determinant Cap construction uses the xn h R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/XiNorm.lean#L545-L583
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/XiNorm.lean#L545-L583

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

theorem Formalism.BranchingDeterminantCap.xn_hR {μ : Fin n → ℕ} {f : MvPolynomial (Fin r × Fin n) ℂ} (hf : f ∈ dualWeyl ℂ r n μ)
    (t s : Fin n) (hts : t < s) : ∑ b : Fin r, X (b, t) * pderiv (b, s) f = 0 := by sorry
