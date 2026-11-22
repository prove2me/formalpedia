-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_xn_sum_perm
-- name    : Formalism.BranchingDeterminantCap.xn_sum_perm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:27:04.991952+00:00
-- url     : https://prove2.me/theorems/361453a8-ed2a-452e-8878-289352247a50
-- title:
--   Branching Determinant Cap: xn sum perm
-- statement:
--   The Branching Determinant Cap construction uses the xn sum perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/XiNorm.lean#L456-L465
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/XiNorm.lean#L456-L465

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

theorem Formalism.BranchingDeterminantCap.xn_sum_perm (ι : κ → Fin r) (f : MvPolynomial (Fin r × Fin n) ℂ) (p : ℕ) (hp : p ≤ n)
    (J : Fin p → κ) (hJ : Function.Injective J) :
    ∑ a ∈ (Finset.univ : Finset (Equiv.Perm (Fin p))).image (fun π : Equiv.Perm (Fin p) => J ∘ π),
      xnN (initMinor ℂ (ι ∘ a) hp * f) = (p.factorial : ℝ) * xnN (initMinor ℂ (ι ∘ J) hp * f) := by sorry
