-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bs_extM_conj
-- name    : Formalism.BranchingDeterminantCap.bs_extM_conj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:26:29.990584+00:00
-- url     : https://prove2.me/theorems/dc947e90-72cf-4ed8-bc61-23c67dea3df5
-- title:
--   Branching Determinant Cap: bs ext M conj
-- statement:
--   The Branching Determinant Cap construction uses the bs ext M conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchScale.lean#L286-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchScale.lean#L286-L295

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

theorem Formalism.BranchingDeterminantCap.bs_extM_conj {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    (extM ℂ g).conjTranspose = extM ℂ g.conjTranspose := by sorry
