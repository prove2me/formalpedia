-- Prove2me | Theorems.Thm_Formalism_LIFT_uc_pull_xn
-- name    : Formalism.LIFT.uc_pull_xn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:10:12.664594+00:00
-- url     : https://prove2.me/theorems/aac01690-a01f-47c3-8ab1-97419f61cb00
-- title:
--   LIFT: uc pull xn
-- statement:
--   The LIFT construction uses the uc pull xn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/UChase.lean#L179-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/UChase.lean#L179-L186

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

theorem Formalism.LIFT.uc_pull_xn (S : SES W₀ W₁ W₂) {m : D₁} (hm : m ∈ W₁.N) (h0 : S.π.f (B.X • m) = 0) :
    ∃ m₀ ∈ W₀.N, S.ι.f (B.X • m₀) = B.X • m := by sorry
