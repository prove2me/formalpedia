-- Prove2me | Theorems.Thm_Formalism_LIFT_comp_mem
-- name    : Formalism.LIFT.comp_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:09:13.743251+00:00
-- url     : https://prove2.me/theorems/a2395eaa-3ca9-47c8-9c48-ac65cf882b67
-- title:
--   LIFT: comp mem
-- statement:
--   The LIFT construction uses the comp mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/CompsOfMemMap.lean#L97-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/CompsOfMemMap.lean#L97-L104

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

theorem Formalism.LIFT.comp_mem (hℓ : 0 < ℓ) (hε : φA ε = ε ^ ℓ)
    (hU : ∀ g : A, ∃! e : Fin ℓ → A, g = ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i))
    {x : A} (hx : x ∈ Ideal.map φA aa) (e : Fin ℓ → A)
    (he : x = ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i)) (i : Fin ℓ) : e i ∈ aa := by sorry
