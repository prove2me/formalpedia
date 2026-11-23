-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_xn_sum_castLE
-- name    : Formalism.BranchingDeterminantCap.xn_sum_castLE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:47.769621+00:00
-- url     : https://prove2.me/theorems/60ddc7a3-be1e-4eaf-bed7-9431689e6633
-- title:
--   Branching Determinant Cap: xn sum cast LE
-- statement:
--   The Branching Determinant Cap construction uses the xn sum cast LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/XiNorm.lean#L612-L623
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/XiNorm.lean#L612-L623

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

theorem Formalism.BranchingDeterminantCap.xn_sum_castLE {A : Type*} [AddCommMonoid A] {k : ℕ} (hk : k ≤ r) (g : Fin r → A)
    (hg : ∀ b : Fin r, k ≤ b.val → g b = 0) :
    ∑ b : Fin k, g (Fin.castLE hk b) = ∑ b : Fin r, g b := by sorry
