-- Prove2me | Theorems.Thm_Formalism_LIFT_GradedDegree_graded_prod
-- name    : Formalism.LIFT.GradedDegree.graded_prod
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:13:29.403236+00:00
-- url     : https://prove2.me/theorems/3de65174-c7c5-4908-ac84-fadb275fcb14
-- title:
--   Graded Degree: graded prod
-- statement:
--   The Graded Degree construction uses the graded prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/Graded.lean#L97-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/Graded.lean#L97-L110

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_Graded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LIFT
open Formalism.LIFT.GradedDegree
variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A] {B : Base ℓ A} {M : ℕ}

theorem Formalism.LIFT.GradedDegree.graded_prod (hG : GradedStep) {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D]
    [IsScalarTower ℤ_[ℓ] A D] (W : WD B M D) (i j : ℕ) (hij : i ≤ j) :
    ∀ m ∈ W.N, ∃ m' ∈ W.N, Polynomial.aeval W.γ
      (∏ k ∈ Finset.Ico i j, (Polynomial.X - Polynomial.C ((B.u : ℤ_[ℓ]) ^ k))) (B.X ^ i • m)
        = B.X ^ j • m' := by sorry
