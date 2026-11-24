-- Prove2me | Theorems.Thm_Formalism_LIFT_uc_hom_xn
-- name    : Formalism.LIFT.uc_hom_xn
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T09:50:21.171813+00:00
-- url     : https://prove2.me/theorems/feddc84b-c29f-426c-b48d-ab021f9ca199
-- title:
--   LIFT: uc hom xn
-- statement:
--   The LIFT construction uses the uc hom xn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/UChase.lean#L140-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/UChase.lean#L140-L142

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
variable {D D' : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
  [AddCommGroup D'] [Module A D'] [Module ℤ_[ℓ] D'] [IsScalarTower ℤ_[ℓ] A D']
  {W : WD B M D} {W' : WD B M D'}

theorem Formalism.LIFT.uc_hom_xn (f : Hom W W') {x : D} (hx : W.XN x) : W'.XN (f.f x) := by sorry
