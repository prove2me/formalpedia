-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_xn_W_ratio
-- name    : Formalism.BranchingDeterminantCap.xn_W_ratio
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:18.185355+00:00
-- url     : https://prove2.me/theorems/7de3f409-f426-43c5-9c19-355b644be0e9
-- title:
--   Branching Determinant Cap: xn W ratio
-- statement:
--   The Branching Determinant Cap construction uses the xn W ratio property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/XiNorm.lean#L693-L703
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/XiNorm.lean#L693-L703

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

theorem Formalism.BranchingDeterminantCap.xn_W_ratio (N : ℕ) (μ : ℕ → ℕ) (p : ℕ) (hp : p ≤ N) (h0 : ∀ j, p ≤ j → μ j = 0) :
    xnW N (xnAdd μ p) * xnC p μ p = xnW N μ * xnC N μ p := by sorry
