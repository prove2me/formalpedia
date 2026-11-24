-- Prove2me | Theorems.Thm_Formalism_LIFT_comps_sum
-- name    : Formalism.LIFT.comps_sum
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T09:50:16.645107+00:00
-- url     : https://prove2.me/theorems/06977ca1-2923-4af1-9ef2-b96d08646f56
-- title:
--   LIFT: comps sum
-- statement:
--   The LIFT construction uses the comps sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/CompsOfMemMap.lean#L60-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/CompsOfMemMap.lean#L60-L62

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

theorem Formalism.LIFT.comps_sum {ι : Type} (s : Finset ι) (f : ι → A) (h : ∀ i ∈ s, Comps φA ε aa ℓ (f i)) :
    Comps φA ε aa ℓ (∑ i ∈ s, f i) := by sorry
