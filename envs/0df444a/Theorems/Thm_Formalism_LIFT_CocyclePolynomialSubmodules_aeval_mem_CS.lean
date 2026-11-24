-- Prove2me | Theorems.Thm_Formalism_LIFT_CocyclePolynomialSubmodules_aeval_mem_CS
-- name    : Formalism.LIFT.CocyclePolynomialSubmodules.aeval_mem_CS
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:58.984774+00:00
-- url     : https://prove2.me/theorems/72ea6f01-9d72-4f1d-b117-ba6fb1d217c1
-- title:
--   Cocycle Polynomial Submodules: aeval mem CS
-- statement:
--   The Cocycle Polynomial Submodules construction uses the aeval mem CS property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/UClaim.lean#L100-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/UClaim.lean#L100-L101

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

theorem Formalism.LIFT.CocyclePolynomialSubmodules.aeval_mem_CS (p : Polynomial ℤ_[ℓ]) {y : D} (hy : y ∈ CS W) :
    Polynomial.aeval W.γ p y ∈ CS W := by sorry
