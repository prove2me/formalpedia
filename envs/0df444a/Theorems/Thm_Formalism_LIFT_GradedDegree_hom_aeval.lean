-- Prove2me | Theorems.Thm_Formalism_LIFT_GradedDegree_hom_aeval
-- name    : Formalism.LIFT.GradedDegree.hom_aeval
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T09:50:14.276979+00:00
-- url     : https://prove2.me/theorems/5e0f9469-7785-46b3-863f-e35e209f791e
-- title:
--   Graded Degree: hom aeval
-- statement:
--   The Graded Degree construction uses the hom aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/Graded.lean#L83-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/Graded.lean#L83-L95

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

theorem Formalism.LIFT.GradedDegree.hom_aeval {D D' : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D]
    [IsScalarTower ℤ_[ℓ] A D] [AddCommGroup D'] [Module A D'] [Module ℤ_[ℓ] D']
    [IsScalarTower ℤ_[ℓ] A D'] {W : WD B M D} {W' : WD B M D'} (f : Hom W W')
    (p : Polynomial ℤ_[ℓ]) : ∀ x, f.f (Polynomial.aeval W.γ p x) = Polynomial.aeval W'.γ p (f.f x) := by sorry
