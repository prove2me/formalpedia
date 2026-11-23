-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_xn_minor_sum
-- name    : Formalism.BranchingDeterminantCap.xn_minor_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:46.118916+00:00
-- url     : https://prove2.me/theorems/cec2889f-27be-43bf-aedb-7a1aa7ebcd1e
-- title:
--   Branching Determinant Cap: xn minor sum
-- statement:
--   The Branching Determinant Cap construction uses the xn minor sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/XiNorm.lean#L184-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/XiNorm.lean#L184-L190

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

theorem Formalism.BranchingDeterminantCap.xn_minor_sum (ι : κ → Fin r) {p : ℕ} (hp : p ≤ n) (a : Fin p → κ) :
    initMinor ℂ (ι ∘ a) hp = ∑ π : Equiv.Perm (Fin p), C (xnSg π) * xnMono ι hp (a ∘ π) := by sorry
