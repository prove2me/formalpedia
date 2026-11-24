-- Prove2me | Theorems.Thm_Formalism_LIFT_uc_pull_qinv
-- name    : Formalism.LIFT.uc_pull_qinv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:09:50.892003+00:00
-- url     : https://prove2.me/theorems/ced59c14-a340-4444-964f-007be92a89d9
-- title:
--   LIFT: uc pull qinv
-- statement:
--   The LIFT construction uses the uc pull qinv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/UChase.lean#L170-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/UChase.lean#L170-L177

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ValProd
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ZpowVal
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_UChase
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
variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A] {B : Base ℓ A} {M : ℕ}
variable {D₀ D₁ D₂ : Type}
    [AddCommGroup D₀] [Module A D₀] [Module ℤ_[ℓ] D₀] [IsScalarTower ℤ_[ℓ] A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module ℤ_[ℓ] D₁] [IsScalarTower ℤ_[ℓ] A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module ℤ_[ℓ] D₂] [IsScalarTower ℤ_[ℓ] A D₂]
    {W₀ : WD B M D₀} {W₁ : WD B M D₁} {W₂ : WD B M D₂}

theorem Formalism.LIFT.uc_pull_qinv (S : SES W₀ W₁ W₂) {y : D₁} (hy : W₁.QInv y) (h0 : S.π.f y = 0) :
    ∃ y₀, W₀.QInv y₀ ∧ S.ι.f y₀ = y := by sorry
