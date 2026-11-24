-- Prove2me | Theorems.Thm_Formalism_LIFT_GradedDegree_aeval_mem
-- name    : Formalism.LIFT.GradedDegree.aeval_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T09:50:15.961337+00:00
-- url     : https://prove2.me/theorems/3becc4aa-3c4e-43e5-8224-f39b2edf9886
-- title:
--   Graded Degree: aeval mem
-- statement:
--   The Graded Degree construction uses the aeval mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/Graded.lean#L68-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/Graded.lean#L68-L81

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

theorem Formalism.LIFT.GradedDegree.aeval_mem {D : Type} [AddCommGroup D] [Module ℤ_[ℓ] D] (g : D →ₗ[ℤ_[ℓ]] D)
    (S : D → Prop) (hadd : ∀ x y, S x → S y → S (x + y))
    (hsmul : ∀ (c : ℤ_[ℓ]) x, S x → S (c • x)) (hg : ∀ x, S x → S (g x))
    (p : Polynomial ℤ_[ℓ]) : ∀ x, S x → S (Polynomial.aeval g p x) := by sorry
