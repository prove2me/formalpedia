-- Prove2me | Theorems.Thm_Formalism_LIFT_GradedDegree_aeval_mul_X
-- name    : Formalism.LIFT.GradedDegree.aeval_mul_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:26:30.797683+00:00
-- url     : https://prove2.me/theorems/31f481ed-b57b-4396-846d-1d7b66fe1541
-- title:
--   Graded Degree: aeval mul X
-- statement:
--   The Graded Degree construction uses the aeval mul X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/Graded.lean#L64-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/Graded.lean#L64-L66

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

theorem Formalism.LIFT.GradedDegree.aeval_mul_X {D : Type} [AddCommGroup D] [Module ℤ_[ℓ] D] (g : D →ₗ[ℤ_[ℓ]] D)
    (p : Polynomial ℤ_[ℓ]) : Polynomial.aeval g (p * Polynomial.X) = Polynomial.aeval g p * g := by sorry
