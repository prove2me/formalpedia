-- Prove2me | Theorems.Thm_Formalism_LIFT_xh_coeffs
-- name    : Formalism.LIFT.xh_coeffs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:10:22.342668+00:00
-- url     : https://prove2.me/theorems/621638c0-0313-4bfb-8fb9-82bf02ee0c46
-- title:
--   LIFT: xh coeffs
-- statement:
--   The LIFT construction uses the xh coeffs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/CompsOfMemMap.lean#L132-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/CompsOfMemMap.lean#L132-L162

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

theorem Formalism.LIFT.xh_coeffs (hℓ : 0 < ℓ) (hε : φA ε = ε ^ ℓ)
    (hU : ∀ g : A, ∃! e : Fin ℓ → A, g = ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i))
    (X Q : A) (H : ℕ) (hX : φA X = X * Q)
    (hQ : ∀ a ∈ aa, Q ^ H * a ∈ Ideal.map φA aa) (n : ℕ) :
    ∀ m : ℕ → ℤ, X ^ H * ∑ k ∈ range (ℓ ^ n), (m k : A) * ε ^ k ∈ aa →
      ∀ k < ℓ ^ n, X ^ H * (m k : A) ∈ aa := by sorry
