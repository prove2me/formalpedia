-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bm_kill
-- name    : Formalism.BranchingDeterminantCap.bm_kill
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:24:32.067527+00:00
-- url     : https://prove2.me/theorems/15757017-a911-4215-872b-ad315ecaa80e
-- title:
--   Branching Determinant Cap: bm kill
-- statement:
--   The Branching Determinant Cap construction uses the bm kill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1182-L1257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1182-L1257

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod

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

theorem Formalism.BranchingDeterminantCap.bm_kill {R σ B : Type*} [CommRing R] [IsDomain R] [CharZero R] [AddCommMonoid B] (w : σ → B) (ω : B → ℤ)
    (C : ℤ → Module.End R (MvPolynomial σ R)) (W : Submodule R (MvPolynomial σ R)) (χ : B → ℤ → ℤ)
    (admitted : B → Prop) (hCC : ∀ u v, Commute (C u) (C v))
    (hCc : ∀ u β, Commute (weightedHomogeneousComponent w β : Module.End R (MvPolynomial σ R)) (C u))
    (hCW : ∀ u, ∀ G ∈ W, C u G ∈ W)
    (hEig : ∀ G ∈ W, ∀ β, weightedHomogeneousComponent w β G ≠ 0 →
      (∀ β', weightedHomogeneousComponent w β' G ≠ 0 → ω β' ≤ ω β) →
      admitted β ∧ ∀ u, C u (weightedHomogeneousComponent w β G) =
        ((χ β u : ℤ) : R) • weightedHomogeneousComponent w β G)
    (hSep : ∀ β β', admitted β → admitted β' → β ≠ β' → ∃ u, χ β u ≠ χ β' u)
    (ℓ : List ℤ) (b : B) (hℓ : ∀ β, admitted β → β ≠ b → ∃ u ∈ ℓ, χ β u = 0)
    (G : MvPolynomial σ R) (hG : G ∈ W) (hb : weightedHomogeneousComponent w b G = 0) :
    (ℓ.map C).prod G = 0 := by sorry
