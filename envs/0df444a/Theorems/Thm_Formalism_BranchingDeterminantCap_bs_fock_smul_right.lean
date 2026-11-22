-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bs_fock_smul_right
-- name    : Formalism.BranchingDeterminantCap.bs_fock_smul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:04:02.938115+00:00
-- url     : https://prove2.me/theorems/0ece4455-aab0-4843-8c64-cfb5f80129e2
-- title:
--   Branching Determinant Cap: bs fock smul right
-- statement:
--   The Branching Determinant Cap construction uses the bs fock smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchScale.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchScale.lean#L15-L17

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

theorem Formalism.BranchingDeterminantCap.bs_fock_smul_right {σ : Type*} (c : ℂ) (f g : MvPolynomial σ ℂ) :
    fockF f (c • g) = star c * fockF f g := by sorry
