-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_xnInv_step
-- name    : Formalism.BranchingDeterminantCap.xnInv_step
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:43.359304+00:00
-- url     : https://prove2.me/theorems/0a147d8f-4193-4afc-8cf9-7ff0e8920220
-- title:
--   Branching Determinant Cap: xn Inv step
-- statement:
--   The Branching Determinant Cap construction uses the xn Inv step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/XiNorm.lean#L763-L816
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/XiNorm.lean#L763-L816

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

theorem Formalism.BranchingDeterminantCap.xnInv_step {k : ℕ} {μ : ℕ → ℕ} {x h : MvPolynomial (Fin r × Fin n) ℂ} (H : xnInv k μ x h)
    (hk : k ≤ n) (hkr : k ≤ r) (J : Fin k → Fin r) (hJ : Function.Injective J) :
    xnInv k (xnAdd μ k) (initMinor ℂ J hk * x) (lpMinor ℂ k hkr hk * h) := by sorry
