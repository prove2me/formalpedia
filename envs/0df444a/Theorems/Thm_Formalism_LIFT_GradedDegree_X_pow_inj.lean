-- Prove2me | Theorems.Thm_Formalism_LIFT_GradedDegree_X_pow_inj
-- name    : Formalism.LIFT.GradedDegree.X_pow_inj
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T09:50:32.986808+00:00
-- url     : https://prove2.me/theorems/89bf5979-b069-49eb-b8fb-c7a45b31c2d7
-- title:
--   Graded Degree: X pow inj
-- statement:
--   The Graded Degree construction uses the X pow inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/Graded.lean#L54-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/Graded.lean#L54-L62

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

theorem Formalism.LIFT.GradedDegree.X_pow_inj {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D]
    [IsScalarTower ℤ_[ℓ] A D] (W : WD B M D) (k : ℕ) (x : D) (h : B.X ^ k • x = 0) : x = 0 := by sorry
