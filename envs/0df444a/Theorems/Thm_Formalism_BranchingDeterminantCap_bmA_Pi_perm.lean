-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmA_Pi_perm
-- name    : Formalism.BranchingDeterminantCap.bmA_Pi_perm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:19:27.123656+00:00
-- url     : https://prove2.me/theorems/174685fd-8655-4b94-aa8b-12dfa41eef59
-- title:
--   Branching Determinant Cap: bm A Pi perm
-- statement:
--   The Branching Determinant Cap construction uses the bm A Pi perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L690-L716
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L690-L716

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}

theorem Formalism.BranchingDeterminantCap.bmA_Pi_perm (E : Fin n → Fin n → Module.End R M) (u : ℤ)
    (hE : ∀ i j k l, E i j * E k l - E k l * E i j = (if j = k then E i l else 0) - (if i = l then E k j else 0))
    (h2 : ∀ x : Module.End R M, x + x = 0 → x = 0) (τ : Equiv.Perm (Fin n)) :
    ∀ β : Fin n → Fin n, bmPi E u (β ∘ τ) = ((Equiv.Perm.sign τ : ℤˣ) : ℤ) • bmPi E u β := by sorry
