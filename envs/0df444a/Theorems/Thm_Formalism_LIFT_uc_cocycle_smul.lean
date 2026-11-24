-- Prove2me | Theorems.Thm_Formalism_LIFT_uc_cocycle_smul
-- name    : Formalism.LIFT.uc_cocycle_smul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T09:50:15.773798+00:00
-- url     : https://prove2.me/theorems/78ab14be-a847-4e9f-84c7-63beaf289d3b
-- title:
--   LIFT: uc cocycle smul
-- statement:
--   The LIFT construction uses the uc cocycle smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/UChase.lean#L114-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/UChase.lean#L114-L117

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
variable {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]

theorem Formalism.LIFT.uc_cocycle_smul (W : WD B M D) (r : ℤ_[ℓ]) {y z : D} (h : W.Cocycle y z) :
    W.Cocycle (r • y) (r • z) := by sorry
