-- Prove2me | Theorems.Thm_Formalism_LIFT_xh_comp
-- name    : Formalism.LIFT.xh_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:09:59.305496+00:00
-- url     : https://prove2.me/theorems/0293bc8b-0ff3-4f27-b908-ad763b76f28c
-- title:
--   LIFT: xh comp
-- statement:
--   The LIFT construction uses the xh comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/CompsOfMemMap.lean#L106-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/CompsOfMemMap.lean#L106-L118

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

theorem Formalism.LIFT.xh_comp (hℓ : 0 < ℓ) (hε : φA ε = ε ^ ℓ)
    (hU : ∀ g : A, ∃! e : Fin ℓ → A, g = ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i))
    (X Q : A) (H : ℕ) (hX : φA X = X * Q)
    (hQ : ∀ a ∈ aa, Q ^ H * a ∈ Ideal.map φA aa) (e : Fin ℓ → A)
    (h : X ^ H * ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i) ∈ aa) (i : Fin ℓ) :
    X ^ H * e i ∈ aa := by sorry
