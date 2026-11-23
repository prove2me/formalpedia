-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmD_top
-- name    : Formalism.BranchingDeterminantCap.bmD_top
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:20:42.757797+00:00
-- url     : https://prove2.me/theorems/300ee0bf-20ae-4c7c-90e9-ab28269151a3
-- title:
--   Branching Determinant Cap: bm D top
-- statement:
--   The Branching Determinant Cap construction uses the bm D top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1477-L1509
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1477-L1509

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

theorem Formalism.BranchingDeterminantCap.bmD_top {R : Type} [CommRing R] {n : ℕ} (G : BP R n) (β : Fin n → ℤ)
    (hmax : ∀ β', zcomp R n β' G ≠ 0 → omg β' ≤ omg β) (l j : Fin n) (hj : j.val = l.val + 1) (k : ℕ) :
    (∀ β', omg β + (k : ℤ) < omg β' → zcomp R n β' ((ndF R (n + 1) n l j)^[k] G) = 0) ∧
      omg (β + k • (Pi.single j 1 - Pi.single l 1)) = omg β + (k : ℤ) ∧
      zcomp R n (β + k • (Pi.single j 1 - Pi.single l 1)) ((ndF R (n + 1) n l j)^[k] G) =
        (bmZ R n j l)^[k] (zcomp R n β G) := by sorry
