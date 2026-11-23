-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_xn_R
-- name    : Formalism.BranchingDeterminantCap.xn_R
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:04.864208+00:00
-- url     : https://prove2.me/theorems/981abdec-038a-4f25-9999-b9b2d3093fb3
-- title:
--   Branching Determinant Cap: xn R
-- statement:
--   The Branching Determinant Cap construction uses the xn R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/XiNorm.lean#L645-L673
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/XiNorm.lean#L645-L673

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

theorem Formalism.BranchingDeterminantCap.xn_R (μ : ℕ → ℕ) (p i : ℕ) (hi : i < p) (h0 : ∀ j, p ≤ j → μ j = 0) (m : ℕ) (hm : p ≤ m) :
    (∏ j ∈ Finset.range m, xnT (xnAdd μ p) i j) * ((p : ℝ) - i + μ i) =
      (∏ j ∈ Finset.range m, xnT μ i j) * ((m : ℝ) - i + μ i) := by sorry
