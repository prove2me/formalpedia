-- Prove2me | Theorems.Thm_Formalism_LIFT_CocyclePolynomialSubmodules_tors_free
-- name    : Formalism.LIFT.CocyclePolynomialSubmodules.tors_free
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T09:50:37.065854+00:00
-- url     : https://prove2.me/theorems/13408d57-019c-4528-b630-fe76043409b1
-- title:
--   Cocycle Polynomial Submodules: tors free
-- statement:
--   The Cocycle Polynomial Submodules construction uses the tors free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/UClaim.lean#L108-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/UClaim.lean#L108-L129

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

theorem Formalism.LIFT.CocyclePolynomialSubmodules.tors_free (h4 : ∀ y, W.QInv y → (ℓ : ℤ_[ℓ]) • y ∈ W.N → y ∈ W.N)
    {c : ℤ_[ℓ]} (hc : c ≠ 0) {y : D} (hy : y ∈ QS W) (hcy : c • y ∈ W.N) : y ∈ W.N := by sorry
