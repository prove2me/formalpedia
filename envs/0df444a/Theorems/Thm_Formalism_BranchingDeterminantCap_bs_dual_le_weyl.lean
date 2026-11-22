-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bs_dual_le_weyl
-- name    : Formalism.BranchingDeterminantCap.bs_dual_le_weyl
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:08:22.322614+00:00
-- url     : https://prove2.me/theorems/38b75d2e-49a4-4f16-8d47-c1e2057de054
-- title:
--   Branching Determinant Cap: bs dual le weyl
-- statement:
--   The Branching Determinant Cap construction uses the bs dual le weyl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchScale.lean#L53-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchScale.lean#L53-L60

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

theorem Formalism.BranchingDeterminantCap.bs_dual_le_weyl {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) :
    dualWeyl ℂ r n ν ≤ weyl ℂ r n hn ν := by sorry
