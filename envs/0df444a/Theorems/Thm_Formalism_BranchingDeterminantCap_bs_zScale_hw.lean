-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bs_zScale_hw
-- name    : Formalism.BranchingDeterminantCap.bs_zScale_hw
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:26:41.113193+00:00
-- url     : https://prove2.me/theorems/65139729-48e9-4515-95c7-e5c251c0f619
-- title:
--   Branching Determinant Cap: bs z Scale hw
-- statement:
--   The Branching Determinant Cap construction uses the bs z Scale hw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchScale.lean#L361-L379
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchScale.lean#L361-L379

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchScale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
open Formalism.REAL
noncomputable section
open Formalism Formalism.BranchingDeterminantCap

theorem Formalism.BranchingDeterminantCap.bs_zScale_hw (n : ℕ) (lam : Fin n → ℕ) (t : ℝ) :
    rowAct ℂ (zScale n t) (hw ℂ (Nat.le_succ n) lam) = hw ℂ (Nat.le_succ n) lam := by sorry
