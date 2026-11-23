-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmA_four_mid
-- name    : Formalism.BranchingDeterminantCap.bmA_four_mid
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:20:33.024927+00:00
-- url     : https://prove2.me/theorems/8e05313c-5ded-4569-b649-d15aaa5a1e9c
-- title:
--   Branching Determinant Cap: bm A four mid
-- statement:
--   The Branching Determinant Cap construction uses the bm A four mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L606-L617
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L606-L617

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

theorem Formalism.BranchingDeterminantCap.bmA_four_mid (E : Fin n → Fin n → Module.End R M) (u : ℤ)
    (hE : ∀ i j k l, E i j * E k l - E k l * E i j = (if j = k then E i l else 0) - (if i = l then E k j else 0))
    (p p' : Fin n) (hp : p'.val = p.val + 1) (a b i j : Fin n) :
    bmF E u p a i * bmF E u p' b j - bmF E u p b j * bmF E u p' a i =
      bmF E u p b i * bmF E u p' a j - bmF E u p a j * bmF E u p' b i := by sorry
