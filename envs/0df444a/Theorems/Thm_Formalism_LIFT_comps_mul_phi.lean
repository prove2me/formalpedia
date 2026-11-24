-- Prove2me | Theorems.Thm_Formalism_LIFT_comps_mul_phi
-- name    : Formalism.LIFT.comps_mul_phi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:09:06.629252+00:00
-- url     : https://prove2.me/theorems/d7964798-2f49-4040-b676-24322c38a25b
-- title:
--   LIFT: comps mul phi
-- statement:
--   The LIFT construction uses the comps mul phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/CompsOfMemMap.lean#L26-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/CompsOfMemMap.lean#L26-L32

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

theorem Formalism.LIFT.comps_mul_phi (s : A) {x : A} (hx : Comps φA ε aa ℓ x) :
    Comps φA ε aa ℓ (φA s * x) := by sorry
