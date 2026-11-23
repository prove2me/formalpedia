-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmZ_iter_inj
-- name    : Formalism.BranchingDeterminantCap.bmZ_iter_inj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:24:41.489997+00:00
-- url     : https://prove2.me/theorems/c9dcfb4d-617f-4b92-b218-0375c25200cf
-- title:
--   Branching Determinant Cap: bm Z iter inj
-- statement:
--   The Branching Determinant Cap construction uses the bm Z iter inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L461-L476
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L461-L476

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

theorem Formalism.BranchingDeterminantCap.bmZ_iter_inj (R : Type*) [CommRing R] [IsDomain R] [CharZero R] (n : ℕ) (j l : Fin n) (hjl : j ≠ l)
    (k : ℕ) (β : Fin n → ℤ) (F : BP R n) (hF : IsWeightedHomogeneous (zW n) F β) (hk : (k : ℤ) ≤ β l)
    (h0 : (bmZ R n j l)^[k] F = 0) : F = 0 := by sorry
