-- Prove2me | Theorems.Thm_Formalism_LIFT_sum_split
-- name    : Formalism.LIFT.sum_split
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T09:49:59.986743+00:00
-- url     : https://prove2.me/theorems/728e28a7-f3c1-4f94-9697-9b73b3027e5a
-- title:
--   LIFT: sum split
-- statement:
--   The LIFT construction uses the sum split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/CompsOfMemMap.lean#L120-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/CompsOfMemMap.lean#L120-L130

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_CompsOfMemMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LIFT
open Finset
variable {ℓ : ℕ} {A : Type} [CommRing A] (φA : A →+* A) (ε : A) (aa : Ideal A)

theorem Formalism.LIFT.sum_split {M : Type} [AddCommMonoid M] (F : ℕ → M) (a N : ℕ) :
    ∑ i : Fin a, ∑ j ∈ range N, F (i + a * j) = ∑ k ∈ range (a * N), F k := by sorry
