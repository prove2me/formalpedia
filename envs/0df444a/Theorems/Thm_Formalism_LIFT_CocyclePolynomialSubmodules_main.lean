-- Prove2me | Theorems.Thm_Formalism_LIFT_CocyclePolynomialSubmodules_main
-- name    : Formalism.LIFT.CocyclePolynomialSubmodules.main
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:06:12.387893+00:00
-- url     : https://prove2.me/theorems/4ac5038d-0838-455d-8e4c-942439c1db71
-- title:
--   Cocycle Polynomial Submodules: main
-- statement:
--   The Cocycle Polynomial Submodules construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/UClaim.lean#L131-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/UClaim.lean#L131-L190

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ZpowVal
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_UClaim
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
open Formalism.LIFT.CocyclePolynomialSubmodules
variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A]
  {B : Base ℓ A} {M : ℕ} {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D]
  [IsScalarTower ℤ_[ℓ] A D] (W : WD B M D)

theorem Formalism.LIFT.CocyclePolynomialSubmodules.main (P : Polynomial ℤ_[ℓ]) (cG : ℤ_[ℓ]) (hcG : cG ≠ 0)
    (hU : ∀ n ∈ W.N, ∃ x ∈ W.N, ∃ n' ∈ W.N,
      cG • (B.X • n) = (W.γ (B.X • x) - B.X • x) + B.X ^ (M + 1) • n')
    (h1 : ∀ n ∈ W.N, ∃ z ∈ W.N, B.X ^ (M + 1) • n = B.X ^ (M + 1) • z - W.φ (B.X ^ (M + 1) • z))
    (h2 : ∀ y, W.QInv y → B.X • y ∈ W.N → y ∈ W.N)
    (h3 : ∀ y, W.QInv y → Polynomial.aeval W.γ ((Polynomial.X - 1) * P) y ∈ W.N)
    (h4 : ∀ y, W.QInv y → (ℓ : ℤ_[ℓ]) • y ∈ W.N → y ∈ W.N) :
    W.TorsKilled (P.eval 1 * cG) := by sorry
