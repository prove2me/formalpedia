-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bs_antitone
-- name    : Formalism.BranchingDeterminantCap.bs_antitone
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:25:45.254013+00:00
-- url     : https://prove2.me/theorems/5ac1c45d-4a7e-42dd-ac0e-ea59fd0fa2b9
-- title:
--   Branching Determinant Cap: bs antitone
-- statement:
--   The Branching Determinant Cap construction uses the bs antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchScale.lean#L336-L359
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchScale.lean#L336-L359

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

theorem Formalism.BranchingDeterminantCap.bs_antitone {n : ℕ} (lam sg : Fin n → ℕ) (h : Interlace (lamZ lam) (fun i => (sg i : ℤ))) :
    Antitone sg := by sorry
