-- Prove2me | Theorems.Thm_Formalism_LIFT_comps_phi
-- name    : Formalism.LIFT.comps_phi
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T09:50:21.340203+00:00
-- url     : https://prove2.me/theorems/b4de68e2-9f3b-4ffb-a891-2a527e612781
-- title:
--   LIFT: comps phi
-- statement:
--   The LIFT construction uses the comps phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/CompsOfMemMap.lean#L73-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/CompsOfMemMap.lean#L73-L83

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

theorem Formalism.LIFT.comps_phi (hℓ : 0 < ℓ) {a : A} (ha : a ∈ aa) : Comps φA ε aa ℓ (φA a) := by sorry
