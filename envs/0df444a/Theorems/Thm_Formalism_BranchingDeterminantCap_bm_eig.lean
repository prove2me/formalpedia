-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bm_eig
-- name    : Formalism.BranchingDeterminantCap.bm_eig
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:24:21.709804+00:00
-- url     : https://prove2.me/theorems/11030772-1672-47b1-aa97-3eca442666af
-- title:
--   Branching Determinant Cap: bm eig
-- statement:
--   The Branching Determinant Cap construction uses the bm eig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1511-L1583
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1511-L1583

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

theorem Formalism.BranchingDeterminantCap.bm_eig {R : Type} [CommRing R] [IsDomain R] [CharZero R] {n : ℕ} (lam : Fin n → ℕ) (d : ℕ) (G : BP R n)
    (hG : G ∈ dualWeyl R (n + 1) n lam) (hd : IsWeightedHomogeneous (lastW n) G d) (β : Fin n → ℤ)
    (hβ : zcomp R n β G ≠ 0) (hmax : ∀ β', zcomp R n β' G ≠ 0 → omg β' ≤ omg β) :
    bmAdm lam d β ∧ ∀ u, bmCap R n u (zcomp R n β G) = ((bmChi lam β u : ℤ) : R) • zcomp R n β G := by sorry
